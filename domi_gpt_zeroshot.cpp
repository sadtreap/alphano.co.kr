#include <bits/stdc++.h>
using namespace std;

static constexpr int FIRST = 0;
static constexpr int SECOND = 1;
static constexpr int HN = 56;
static constexpr int VN = 56;
static constexpr int SCALE = 16;
static constexpr int INF = 1000000000;
static constexpr int NO_MOVE = -100;

struct Domino {
    uint64_t mask = 0;
    uint64_t affH = 0;
    uint64_t affV = 0;
    int score = 0;
    int x = 0, y = 0;
    int c1 = 0, c2 = 0;
    int pos = 0;
    int tie = 0;
};

static int A[64];
static Domino HM[HN], VM[VN];
static int Hid[8][8], Vid[8][8];
static uint64_t cellAffH[64], cellAffV[64];
static int historyScore[2][56];

static inline int popc(uint64_t x) { return __builtin_popcountll(x); }
static inline int ctz(uint64_t x) { return __builtin_ctzll(x); }

static uint64_t splitmix64(uint64_t x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

static int cellPosValue(int idx) {
    int r = idx / 8, c = idx % 8;
    int vr = min(r, 7 - r);
    int vc = min(c, 7 - c);
    return vr + vc;
}

static void initMoves() {
    memset(Hid, -1, sizeof(Hid));
    memset(Vid, -1, sizeof(Vid));
    memset(cellAffH, 0, sizeof(cellAffH));
    memset(cellAffV, 0, sizeof(cellAffV));

    int id = 0;
    for (int r = 0; r < 8; ++r) {
        for (int c = 0; c < 7; ++c) {
            int a = r * 8 + c, b = a + 1;
            Hid[r][c] = id;
            HM[id].c1 = a; HM[id].c2 = b;
            HM[id].mask = (1ULL << a) | (1ULL << b);
            HM[id].score = A[a] + A[b];
            HM[id].x = r + 1; HM[id].y = c + 1;
            HM[id].pos = cellPosValue(a) + cellPosValue(b);
            HM[id].tie = int(splitmix64(uint64_t(id) * 1315423911ULL) & 7ULL);
            ++id;
        }
    }
    id = 0;
    for (int r = 0; r < 7; ++r) {
        for (int c = 0; c < 8; ++c) {
            int a = r * 8 + c, b = a + 8;
            Vid[r][c] = id;
            VM[id].c1 = a; VM[id].c2 = b;
            VM[id].mask = (1ULL << a) | (1ULL << b);
            VM[id].score = A[a] + A[b];
            VM[id].x = r + 1; VM[id].y = c + 1;
            VM[id].pos = cellPosValue(a) + cellPosValue(b);
            VM[id].tie = int(splitmix64(uint64_t(id + 1000) * 2654435761ULL) & 7ULL);
            ++id;
        }
    }

    for (int i = 0; i < HN; ++i) {
        cellAffH[HM[i].c1] |= (1ULL << i);
        cellAffH[HM[i].c2] |= (1ULL << i);
    }
    for (int i = 0; i < VN; ++i) {
        cellAffV[VM[i].c1] |= (1ULL << i);
        cellAffV[VM[i].c2] |= (1ULL << i);
    }
    for (int i = 0; i < HN; ++i) {
        HM[i].affH = cellAffH[HM[i].c1] | cellAffH[HM[i].c2];
        HM[i].affV = cellAffV[HM[i].c1] | cellAffV[HM[i].c2];
    }
    for (int i = 0; i < VN; ++i) {
        VM[i].affH = cellAffH[VM[i].c1] | cellAffH[VM[i].c2];
        VM[i].affV = cellAffV[VM[i].c1] | cellAffV[VM[i].c2];
    }
}

struct TTEntry {
    uint64_t key = 0;
    int value = 0;
    int16_t depth = -1;
    int8_t flag = 0;
    int8_t best = (int8_t)NO_MOVE;
};

static constexpr int TT_BITS = 22;
static constexpr int TT_SIZE = 1 << TT_BITS;
static constexpr int TT_MASK = TT_SIZE - 1;
static vector<TTEntry> TT;

struct TimeUp {};

struct OrderedMove {
    int id;
    int ord;
};

struct Bot {
    int me = FIRST;
    int currentRel2 = 0;
    chrono::steady_clock::time_point deadline;
    long long nodes = 0;

    inline void checkTime() {
        if ((++nodes & 4095LL) == 0) {
            if (chrono::steady_clock::now() >= deadline) throw TimeUp();
        }
    }

    inline uint64_t makeKey(uint64_t occ, int player, bool prevPass) const {
        uint64_t x = occ;
        x ^= player ? 0x6a09e667f3bcc909ULL : 0xbb67ae8584caa73bULL;
        if (prevPass) x ^= 0x3c6ef372fe94f82bULL;
        if (me == SECOND) x ^= 0xa54ff53a5f1d36f1ULL;
        return splitmix64(x);
    }

    static inline void applyDomino(const Domino &d, uint64_t occ, uint64_t hLegal, uint64_t vLegal,
                                   uint64_t &nOcc, uint64_t &nH, uint64_t &nV) {
        nOcc = occ | d.mask;
        nH = hLegal & ~d.affH;
        nV = vLegal & ~d.affV;
    }

    int maxHorizontalPotential(uint64_t occ) const {
        int total = 0;
        for (int r = 0; r < 8; ++r) {
            int dp[10] = {};
            int rowMask = int((occ >> (r * 8)) & 255ULL);
            for (int c = 7; c >= 0; --c) {
                dp[c] = dp[c + 1];
                if (c < 7 && ((rowMask & (1 << c)) == 0) && ((rowMask & (1 << (c + 1))) == 0)) {
                    int s = A[r * 8 + c] + A[r * 8 + c + 1] + dp[c + 2];
                    if (s > dp[c]) dp[c] = s;
                }
            }
            total += dp[0];
        }
        return total;
    }

    int maxVerticalPotential(uint64_t occ) const {
        int total = 0;
        for (int c = 0; c < 8; ++c) {
            int dp[10] = {};
            for (int r = 7; r >= 0; --r) {
                dp[r] = dp[r + 1];
                if (r < 7) {
                    int a = r * 8 + c, b = a + 8;
                    if (((occ >> a) & 1ULL) == 0 && ((occ >> b) & 1ULL) == 0) {
                        int s = A[a] + A[b] + dp[r + 2];
                        if (s > dp[r]) dp[r] = s;
                    }
                }
            }
            total += dp[0];
        }
        return total;
    }

    int topSum(uint64_t bits, bool horizontal, int k, int &best) const {
        int cnt[7] = {};
        while (bits) {
            int id = ctz(bits);
            bits &= bits - 1;
            int s = horizontal ? HM[id].score : VM[id].score;
            ++cnt[s];
        }
        int sum = 0;
        best = 0;
        int need = k;
        for (int s = 6; s >= 0; --s) {
            if (cnt[s] && best == 0) best = s;
            int take = min(need, cnt[s]);
            sum += take * s;
            need -= take;
            if (need == 0) break;
        }
        return sum;
    }

    int evaluate(uint64_t occ, uint64_t hLegal, uint64_t vLegal, int player, bool prevPass) const {
        int hPot = maxHorizontalPotential(occ);
        int vPot = maxVerticalPotential(occ);
        int hBest = 0, vBest = 0;
        int hTop = topSum(hLegal, true, 3, hBest);
        int vTop = topSum(vLegal, false, 3, vBest);

        int fv = SCALE * (hPot - vPot);
        fv += 2 * (popc(hLegal) - popc(vLegal));
        fv += 3 * (hTop - vTop);
        fv += (player == FIRST ? 6 * hBest : -6 * vBest);

        int val = (me == FIRST) ? fv : -fv;
        if (prevPass) {
            if (player == me) val = max(val, 0);
            else val = min(val, 0);
        }
        return val;
    }

    int orderValue(int player, int id, uint64_t hLegal, uint64_t vLegal, bool prevPass, int ttBest) const {
        bool maxNode = (player == me);
        if (id == -1) {
            int ord = 0;
            if (id == ttBest) ord += maxNode ? 100000000 : -100000000;
            return ord;
        }
        const Domino &d = (player == FIRST) ? HM[id] : VM[id];
        uint64_t curLegal = (player == FIRST) ? hLegal : vLegal;
        uint64_t oppLegal = (player == FIRST) ? vLegal : hLegal;
        uint64_t curAff = (player == FIRST) ? d.affH : d.affV;
        uint64_t oppAff = (player == FIRST) ? d.affV : d.affH;
        int selfLost = popc(curLegal & curAff);
        int oppLost = popc(oppLegal & oppAff);

        int moverGain = SCALE * d.score + 6 * oppLost - 2 * selfLost + d.pos + d.tie;
        moverGain += historyScore[player][id] / 64;
        int botValue = (player == me) ? moverGain : -moverGain;
        if (id == ttBest) botValue += maxNode ? 100000000 : -100000000;
        (void)prevPass;
        return botValue;
    }

    int makeMoveList(int player, bool prevPass, uint64_t hLegal, uint64_t vLegal, int ttBest, OrderedMove out[57]) const {
        uint64_t bits = (player == FIRST) ? hLegal : vLegal;
        int n = 0;
        while (bits) {
            int id = ctz(bits);
            bits &= bits - 1;
            out[n++] = {id, orderValue(player, id, hLegal, vLegal, prevPass, ttBest)};
        }
        if (prevPass) out[n++] = {-1, orderValue(player, -1, hLegal, vLegal, prevPass, ttBest)};

        bool maxNode = (player == me);
        sort(out, out + n, [maxNode](const OrderedMove &a, const OrderedMove &b) {
            if (a.ord != b.ord) return maxNode ? (a.ord > b.ord) : (a.ord < b.ord);
            return a.id < b.id;
        });
        return n;
    }

    int search(uint64_t occ, uint64_t hLegal, uint64_t vLegal, int player, bool prevPass,
               int depth, int alpha, int beta) {
        checkTime();

        uint64_t legal = (player == FIRST) ? hLegal : vLegal;
        if ((hLegal | vLegal) == 0) return 0;
        if (legal == 0) {
            if (prevPass) return 0;
            return search(occ, hLegal, vLegal, player ^ 1, true, depth, alpha, beta);
        }

        uint64_t key = makeKey(occ, player, prevPass);
        TTEntry &ent = TT[key & TT_MASK];
        int ttBest = NO_MOVE;
        int origAlpha = alpha, origBeta = beta;
        if (ent.depth >= 0 && ent.key == key) {
            ttBest = ent.best;
            if (ent.depth >= depth) {
                int v = ent.value;
                if (ent.flag == 0) return v;
                if (ent.flag == 1) alpha = max(alpha, v);
                else if (ent.flag == 2) beta = min(beta, v);
                if (alpha >= beta) return v;
            }
        }

        if (depth <= 0) {
            int v = evaluate(occ, hLegal, vLegal, player, prevPass);
            if (ent.key != key || ent.depth <= 0) {
                ent.key = key; ent.value = v; ent.depth = 0; ent.flag = 0; ent.best = (int8_t)NO_MOVE;
            }
            return v;
        }

        bool maxNode = (player == me);
        OrderedMove moves[57];
        int n = makeMoveList(player, prevPass, hLegal, vLegal, ttBest, moves);

        int bestMove = NO_MOVE;
        int bestVal = maxNode ? -INF : INF;
        int emptyCells = 64 - popc(occ);
        bool allowReduceAtNode = (depth + 2 < emptyCells / 2 + 4);

        for (int mi = 0; mi < n; ++mi) {
            int id = moves[mi].id;
            int val;
            if (id == -1) {
                val = 0;
            } else {
                const Domino &d = (player == FIRST) ? HM[id] : VM[id];
                uint64_t nOcc, nH, nV;
                applyDomino(d, occ, hLegal, vLegal, nOcc, nH, nV);
                int reward = (player == me) ? SCALE * d.score : -SCALE * d.score;
                int childDepth = depth - 1;
                bool reduced = false;
                if (allowReduceAtNode && depth >= 6 && mi >= 8 && n >= 12 && id != ttBest) {
                    childDepth = depth - 2;
                    reduced = true;
                }
                int child = search(nOcc, nH, nV, player ^ 1, false, childDepth,
                                   alpha - reward, beta - reward);
                val = reward + child;
                if (reduced && ((maxNode && val > alpha) || (!maxNode && val < beta))) {
                    child = search(nOcc, nH, nV, player ^ 1, false, depth - 1,
                                   alpha - reward, beta - reward);
                    val = reward + child;
                }
            }

            if (maxNode) {
                if (val > bestVal) { bestVal = val; bestMove = id; }
                if (val > alpha) alpha = val;
                if (alpha >= beta) {
                    if (id >= 0) {
                        int &hs = historyScore[player][id];
                        hs += depth * depth;
                        if (hs > 1000000) hs = 1000000;
                    }
                    break;
                }
            } else {
                if (val < bestVal) { bestVal = val; bestMove = id; }
                if (val < beta) beta = val;
                if (alpha >= beta) {
                    if (id >= 0) {
                        int &hs = historyScore[player][id];
                        hs += depth * depth;
                        if (hs > 1000000) hs = 1000000;
                    }
                    break;
                }
            }
        }

        int flag = 0;
        if (bestVal <= origAlpha) flag = 2;
        else if (bestVal >= origBeta) flag = 1;
        else flag = 0;

        if (ent.key != key || depth >= ent.depth) {
            ent.key = key;
            ent.value = bestVal;
            ent.depth = (int16_t)min(depth, 32767);
            ent.flag = (int8_t)flag;
            ent.best = (int8_t)bestMove;
        }
        return bestVal;
    }

    pair<int,int> rootSearch(uint64_t occ, uint64_t hLegal, uint64_t vLegal, bool prevPass, int depth) {
        int player = me;
        uint64_t legal = (player == FIRST) ? hLegal : vLegal;
        if ((hLegal | vLegal) == 0 || legal == 0) return {-1, 0};

        uint64_t key = makeKey(occ, player, prevPass);
        int ttBest = NO_MOVE;
        TTEntry &ent = TT[key & TT_MASK];
        if (ent.depth >= 0 && ent.key == key) ttBest = ent.best;

        OrderedMove moves[57];
        int n = makeMoveList(player, prevPass, hLegal, vLegal, ttBest, moves);
        int bestId = moves[0].id;
        int bestVal = -INF;
        int alpha = -INF, beta = INF;

        for (int mi = 0; mi < n; ++mi) {
            int id = moves[mi].id;
            int val;
            if (id == -1) {
                val = 0;
            } else {
                const Domino &d = (player == FIRST) ? HM[id] : VM[id];
                uint64_t nOcc, nH, nV;
                applyDomino(d, occ, hLegal, vLegal, nOcc, nH, nV);
                int reward = SCALE * d.score;
                int child = search(nOcc, nH, nV, player ^ 1, false, depth - 1,
                                   alpha - reward, beta - reward);
                val = reward + child;
            }
            if (val > bestVal) { bestVal = val; bestId = id; }
            if (val > alpha) alpha = val;
        }
        return {bestId, bestVal};
    }

    int staticFallback(uint64_t occ, uint64_t hLegal, uint64_t vLegal, bool prevPass) const {
        int player = me;
        uint64_t legal = (player == FIRST) ? hLegal : vLegal;
        if (legal == 0) return -1;
        int bestId = -1;
        int bestVal = prevPass ? 0 : -INF;
        uint64_t bits = legal;
        while (bits) {
            int id = ctz(bits);
            bits &= bits - 1;
            const Domino &d = (player == FIRST) ? HM[id] : VM[id];
            uint64_t nOcc, nH, nV;
            applyDomino(d, occ, hLegal, vLegal, nOcc, nH, nV);
            int val = SCALE * d.score + evaluate(nOcc, nH, nV, player ^ 1, false);
            if (val > bestVal) { bestVal = val; bestId = id; }
        }
        if (prevPass && currentRel2 > 0 && bestVal <= 2 * SCALE) return -1;
        return bestId;
    }

    int computeBudgetMs(int myTimeMs, int emptyCells, int legalCnt, bool prevPass) const {
        int safety = (myTimeMs > 2000 ? 80 : (myTimeMs > 500 ? 50 : 20));
        int usable = max(1, myTimeMs - safety);
        int remOwnTurns = max(1, emptyCells / 4 + 2);
        int budget = max(20, usable / remOwnTurns);
        if (prevPass) budget = max(budget, usable / 6);
        if (emptyCells <= 20) budget = max(budget, usable / 3);
        else if (emptyCells <= 32) budget = max(budget, usable / 8);
        if (legalCnt <= 6) budget = max(budget, usable / 5);
        int cap = (emptyCells <= 16 ? 3500 : 1800);
        budget = min(budget, cap);
        budget = min(budget, usable);
        return max(1, budget);
    }

    int chooseMove(uint64_t occ, uint64_t hLegal, uint64_t vLegal, bool prevPass, int myTimeMs, int oppTimeMs) {
        (void)oppTimeMs;
        uint64_t legal = (me == FIRST) ? hLegal : vLegal;
        if (legal == 0) return -1;
        int fallback = staticFallback(occ, hLegal, vLegal, prevPass);

        int emptyCells = 64 - popc(occ);
        int legalCnt = popc(legal);
        int budget = computeBudgetMs(myTimeMs, emptyCells, legalCnt, prevPass);
        auto start = chrono::steady_clock::now();
        deadline = start + chrono::milliseconds(budget);
        nodes = 0;

        int best = fallback;
        int bestVal = -INF;
        int completedDepth = 0;
        int maxDepth = min(64, emptyCells / 2 + 4);

        for (int depth = 1; depth <= maxDepth; ++depth) {
            try {
                auto res = rootSearch(occ, hLegal, vLegal, prevPass, depth);
                best = res.first;
                bestVal = res.second;
                completedDepth = depth;
            } catch (const TimeUp&) {
                break;
            }
            if (chrono::steady_clock::now() >= deadline) break;
        }

        bool exactLikely = (completedDepth >= maxDepth);
        if (prevPass && currentRel2 > 0 && !exactLikely && best != -1 && bestVal <= 2 * SCALE) {
            best = -1;
        }
        return best;
    }

    void updateAfterMove(int player, int id, uint64_t &occ, uint64_t &hLegal, uint64_t &vLegal, bool &lastPass) {
        if (id < 0) {
            lastPass = true;
            return;
        }
        const Domino &d = (player == FIRST) ? HM[id] : VM[id];
        uint64_t nOcc, nH, nV;
        applyDomino(d, occ, hLegal, vLegal, nOcc, nH, nV);
        occ = nOcc; hLegal = nH; vLegal = nV;
        if (player == me) currentRel2 += 2 * d.score;
        else currentRel2 -= 2 * d.score;
        lastPass = false;
    }
};

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    for (int r = 0; r < 8; ++r) {
        for (int c = 0; c < 8; ++c) {
            if (!(cin >> A[r * 8 + c])) return 0;
        }
    }
    initMoves();
    TT.assign(TT_SIZE, TTEntry());

    uint64_t occ = 0;
    uint64_t hLegal = (1ULL << HN) - 1ULL;
    uint64_t vLegal = (1ULL << VN) - 1ULL;
    bool lastPass = false;

    Bot bot;
    string cmd;
    while (cin >> cmd) {
        if (cmd == "READY") {
            string side;
            cin >> side;
            bot.me = (side == "FIRST") ? FIRST : SECOND;
            bot.currentRel2 = (bot.me == FIRST ? -5 : 5);
            cout << "OK" << '\n';
            cout.flush();
        } else if (cmd == "TURN") {
            int myTime, oppTime;
            cin >> myTime >> oppTime;
            int id = bot.chooseMove(occ, hLegal, vLegal, lastPass, myTime, oppTime);
            if (id < 0) {
                cout << "MOVE -1 -1" << '\n';
                cout.flush();
                bot.updateAfterMove(bot.me, -1, occ, hLegal, vLegal, lastPass);
            } else {
                const Domino &d = (bot.me == FIRST) ? HM[id] : VM[id];
                cout << "MOVE " << d.x << ' ' << d.y << '\n';
                cout.flush();
                bot.updateAfterMove(bot.me, id, occ, hLegal, vLegal, lastPass);
            }
        } else if (cmd == "OPP") {
            int x, y, t;
            cin >> x >> y >> t;
            (void)t;
            if (x == -1 && y == -1) {
                bot.updateAfterMove(bot.me ^ 1, -1, occ, hLegal, vLegal, lastPass);
            } else {
                int r = x - 1, c = y - 1;
                int opp = bot.me ^ 1;
                int id = (opp == FIRST) ? Hid[r][c] : Vid[r][c];
                bot.updateAfterMove(opp, id, occ, hLegal, vLegal, lastPass);
            }
        } else if (cmd == "FINISH") {
            return 0;
        } else {
            return 0;
        }
    }
    return 0;
}
