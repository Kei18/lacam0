#include "../include/lacam.hpp"

bool LaCAM::ANYTIME = false;
float LaCAM::RANDOM_INSERT_PROB1 = 0.001;
float LaCAM::RANDOM_INSERT_PROB2 = 0.001;

bool CompareHNodePointers::operator()(const HNode *l, const HNode *r) const
{
  const auto N = l->Q.size();
  for (size_t i = 0; i < N; ++i) {
    if (l->Q[i] != r->Q[i]) return l->Q[i]->id < r->Q[i]->id;
  }
  return false;
}

HNode::HNode(Config _Q, DistTable *D, HNode *_parent, int _g, int _h)
    : Q(std::move(_Q)),
      parent(_parent),
      neighbors(),
      g(_g),
      h(_h),
      f(g + h),
      depth(parent == nullptr ? 0 : parent->depth + 1),
      priorities(Q.size()),
      order(Q.size(), 0),
      search_tree()
{
  if (parent != nullptr) parent->neighbors.insert(this);
  search_tree.push(new LNode());
  const int N = Q.size();
  for (int i = 0; i < N; ++i) {
    // set priorities
    if (parent == nullptr) {
      // initialize
      priorities[i] = (float)D->get(i, Q[i]) / 10000;
    } else {
      // dynamic priorities, akin to PIBT
      if (D->get(i, Q[i]) != 0) {
        priorities[i] = parent->priorities[i] + 1;
      } else {
        priorities[i] = parent->priorities[i] - (int)parent->priorities[i];
      }
    }
  }

  // set order
  auto cmp = [&](int i, int j) { return priorities[i] > priorities[j]; };
  std::iota(order.begin(), order.end(), 0);
  std::sort(order.begin(), order.end(), cmp);
}

HNode::~HNode()
{
  while (!search_tree.empty()) {
    delete search_tree.front();
    search_tree.pop();
  }
}

LNode::LNode() : who(), where(), depth(0) {}

LNode::LNode(LNode *parent, int i, Vertex *v)
    : who(parent->who), where(parent->where), depth(parent->depth + 1)
{
  who.push_back(i);
  where.push_back(v);
}

LNode::~LNode(){};

LaCAM::LaCAM(const Instance *_ins, DistTable *_D, int _verbose,
             const Deadline *_deadline, int _seed)
    : ins(_ins),
      D(_D),
      deadline(_deadline),
      seed(_seed),
      MT(seed),
      rrd(0, 1),
      verbose(_verbose),
      pibt(ins, D, seed),
      H_goal(nullptr),
      OPEN(),
      loop_cnt(0)
{
}

LaCAM::~LaCAM() {}

Solution LaCAM::solve()
{
  solver_info(1, "LaCAM begins");

  // setup search
  auto EXPLORED = std::unordered_map<Config, HNode *, ConfigHasher>();
  HNodes GC_HNodes;

  // insert initial node
  auto H_init = new HNode(ins->starts, D);
  OPEN.push_front(H_init);
  EXPLORED[H_init->Q] = H_init;
  GC_HNodes.push_back(H_init);

  // search loop
  solver_info(2, "search iteration begins");
  while (!OPEN.empty() && !is_expired(deadline)) {
    ++loop_cnt;

    // random insert
    if (H_goal != nullptr) {
      auto r = rrd(MT);
      if (r < RANDOM_INSERT_PROB2 / 2) {
        OPEN.push_front(H_init);
      } else if (r < RANDOM_INSERT_PROB2) {
        auto H = OPEN[get_random_int(MT, 0, OPEN.size() - 1)];
        OPEN.push_front(H);
      }
    }

    // do not pop here!
    auto H = OPEN.front();  // high-level node

    // check upper bounds
    if (H_goal != nullptr && H->f >= H_goal->g) {
      OPEN.pop_front();
      solver_info(5, "prune, g=", H->g, " >= ", H_goal->g);
      OPEN.push_front(H_init);
      continue;
    }

    // check goal condition
    if (H_goal == nullptr && is_same_config(H->Q, ins->goals)) {
      H_goal = H;
      solver_info(2, "found solution, g=", H->g, ", depth=", H->depth);
      if (!ANYTIME) break;
      continue;
    }

    // extract constraints
    if (H->search_tree.empty()) {
      OPEN.pop_front();
      continue;
    }
    auto L = H->search_tree.front();
    H->search_tree.pop();

    // low level search
    if (L->depth < H->Q.size()) {
      const auto i = H->order[L->depth];
      auto &&C = H->Q[i]->actions;
      std::shuffle(C.begin(), C.end(), MT);  // randomize
      for (auto u : C) H->search_tree.push(new LNode(L, i, u));
    }

    // create successors at the high-level search
    auto Q_to = Config(ins->N, nullptr);
    auto res = set_new_config(H, L, Q_to);
    delete L;
    if (!res) continue;

    // check explored list
    auto iter = EXPLORED.find(Q_to);
    if (iter == EXPLORED.end()) {
      // new one -> insert
      const auto g_val = get_g_val(H, Q_to);
      const auto h_val = get_h_val(Q_to);
      auto H_new = new HNode(std::move(Q_to), D, H, g_val, h_val);
      OPEN.push_front(H_new);
      EXPLORED[H_new->Q] = H_new;
      GC_HNodes.push_back(H_new);
    } else {
      // known configuration
      auto H_known = iter->second;
      rewrite(H, H_known);

      if (rrd(MT) >= RANDOM_INSERT_PROB1) {
        OPEN.push_front(iter->second);  // usual
      } else {
        solver_info(3, "random restart");
        OPEN.push_front(H_init);  // sometimes
      }
    }
  }

  // backtrack
  Solution solution;
  {
    auto H = H_goal;
    while (H != nullptr) {
      solution.push_back(H->Q);
      H = H->parent;
    }
    std::reverse(solution.begin(), solution.end());
  }

  // solution
  if (solution.empty()) {
    if (OPEN.empty()) {
      solver_info(2, "fin. unsolvable instance");
    } else {
      solver_info(2, "fin. reach time limit");
    }
  } else {
    if (OPEN.empty()) {
      solver_info(2, "fin. optimal solution, g=", H_goal->g,
                  ", depth=", H_goal->depth);
    } else {
      solver_info(2, "fin. suboptimal solution, g=", H_goal->g,
                  ", depth=", H_goal->depth);
    }
  }

  // end processing
  for (auto &&H : GC_HNodes) delete H;  // memory management

  return solution;
}

bool LaCAM::set_new_config(HNode *H, LNode *L, Config &Q_to)
{
  for (uint d = 0; d < L->depth; ++d) Q_to[L->who[d]] = L->where[d];
  return pibt.set_new_config(H->Q, Q_to, H->order);
}

void LaCAM::rewrite(HNode *H_from, HNode *H_to)
{
  if (!ANYTIME) return;

  // update neighbors
  H_from->neighbors.insert(H_to);

  // Dijkstra
  std::queue<HNode *> Q({H_from});  // queue is sufficient
  while (!Q.empty()) {
    auto n_from = Q.front();
    Q.pop();
    for (auto n_to : n_from->neighbors) {
      auto g_val = n_from->g + get_edge_cost(n_from->Q, n_to->Q);
      if (g_val < n_to->g) {
        if (n_to == H_goal) {
          solver_info(2, "cost update: g=", H_goal->g, " -> ", g_val,
                      ", depth=", H_goal->depth, " -> ", n_from->depth + 1);
        }
        n_to->g = g_val;
        n_to->f = n_to->g + n_to->h;
        n_to->parent = n_from;
        n_to->depth = n_from->depth + 1;
        Q.push(n_to);
        if (H_goal != nullptr && n_to->f < H_goal->f) {
          OPEN.push_front(n_to);
          solver_info(4, "reinsert: g=", n_to->g, " < ", H_goal->g);
        }
      }
    }
  }
}

int LaCAM::get_g_val(HNode *H_parent, const Config &Q_to)
{
  return H_parent->g + get_edge_cost(H_parent->Q, Q_to);
}

int LaCAM::get_h_val(const Config &Q)
{
  auto c = 0;
  for (size_t i = 0; i < ins->N; ++i) c += D->get(i, Q[i]);
  return c;
}

int LaCAM::get_edge_cost(const Config &Q1, const Config &Q2)
{
  auto cost = 0;
  for (size_t i = 0; i < ins->N; ++i) {
    if (Q1[i] != ins->goals[i] || Q2[i] != ins->goals[i]) {
      cost += 1;
    }
  }
  return cost;
}
