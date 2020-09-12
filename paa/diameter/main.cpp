#include <experimental/optional>
#include <iostream>
#include <limits>
#include <stack>
#include <vector>

using namespace std;

/// Given a graph G = (V, E), every edge "e" in E has a weight "w" such that
/// 1 <= w <= 300.
using Weight = uint16_t;
using PathWeight = uint32_t;
/// Value used to represent edges that do not exist in a graph.
PathWeight Inf = numeric_limits<uint32_t>::max();
/// Since we need to compute the shortest path for every pair of vertices in the
/// graph, we shall use the Floyd-Warshall algorithm. Hence, we shall model a
/// graph using an adjacency matrix.
using Graph = vector<vector<Weight>>;
/// Vertices are numbered from 1 to 300 (0 to 299, w.r.t. the matrix).
using Vertex = uint16_t;

struct Result {
    /// The predecessor of a vertex j in the shortest path from i to j. It is
    /// "nil" if there is no such path.
    using Pred = experimental::optional<Vertex>;
    vector<vector<PathWeight>> D;
    vector<vector<Pred>> P;
    Vertex i, j;
    PathWeight diameter;
};

/// Given a graph \p G = (V, E) represented by an adjacency list, this function
/// computes the shortest path between every pair of vertices. It extends the
/// traditional Floyd-Warshall algorithm by producing a matrix P of predecessors
/// that can be used to reconstruct the shortest path. An entry ij in the
/// matrix P, i.e. P[i][j], corresponds to the predecessor of j in the shortest
/// path from vertex i to vertex j. Furthermore, this function also determines
/// a pair of vertices called "diametral vertices", which are the edges of a
/// shortest path that is the maximum between all shortest paths (i.e., the
/// diameter of the graph).
///
/// \returns A quintuple composed by a matrix D of shortest path weights, a
/// matrix P of predecessors, two vertices u and v (the diametral vertices),
/// and the diameter.
Result *floydWarshall(const Graph &G) {
    auto n = G.size();
    auto r = new Result;

    r->D.resize(n);
    r->P.resize(n);

    // Note on the complexity: clearly, the initial setup is O(|V|²).
    for (size_t i = 0; i < n; i++) {
        r->D[i] = vector<PathWeight>(n);
        r->P[i] = vector<Result::Pred>(n);

        for (size_t j = 0; j < n; j++) {
            // Assume that G is already filled with the correct weights.
            // In other words, given an edge ij, G[i][j] = 0 if i == j,
            // Inf if the edge does not exist, or w(i, j) otherwise.
            r->D[i][j] = G[i][j];
            // If i == j or if the edge ij does not exist, there is not
            // predecessor to be defined.
            if (i == j || G[i][j] == Inf)
                r->P[i][j] = experimental::nullopt;
            else
                r->P[i][j] = i;
        }
    }

    // The main Floyd-Warhsall loop, that shall run from k = 0 to n - 1 (or 1
    // to n, in Cormen's pseudocode), is split into a main loop from k = 0 to
    // n - 2, and a separate last iteration for k = n - 1. When k = n - 1,
    // the algorithm is essentially computing the shortest path between all
    // pairs of vertices. This last step can be used to determine a pair of
    // diametral vertices more efficiently.
    //
    // Note on the complexity: clearly, this step runs in O(|V|³).
    for (size_t k = 0; k < n; k++) {
        for (size_t i = 0; i < n; i++) {
            for (size_t j = 0; j < n; j++) {
                // The weight of the path in case "k" is an intermediate node.
                auto withK = r->D[i][k] + r->D[k][j];
                if (r->D[i][j] > withK) {
                    r->D[i][j] = withK;
                    // The predecessor of "j" in the path ij is the same as the
                    // predecessor of "j" in the path kj.
                    r->P[i][j] = r->P[k][j];
                }
            }
        }
    }

    size_t k = n - 1;
    r->diameter = 0;
    for (size_t i = 0; i < n; i++) {
        for (size_t j = 0; j < n; j++) {
            // The weight of the path in case "k" is an intermediate node.
            auto withK = r->D[i][k] + r->D[k][j];
            if (r->D[i][j] > withK) {
                r->D[i][j] = withK;
                // The predecessor of "j" in the path ij is the same as the
                // predecessor of "j" in the path kj.
                r->P[i][j] = r->P[k][j];
            }

            if (r->D[i][j] != Inf && r->D[i][j] > r->diameter) {
                r->diameter = r->D[i][j];
                r->i = i;
                r->j = j;
            }
        }
    }

    return r;
}

/// Takes a matrix of predecessors \p P and two vertices \p u and \p v, and
/// reconstructs the shortest path between u and v.
///
/// \returns a stack of vertices that composes the shortest path. The top of
/// the stack is the vertex "u", while the bottom is "v".
stack<Vertex> reconstructPath(vector<vector<Result::Pred>> P, Vertex i,
                              Vertex j) {
    stack<Vertex> S;
    S.push(j);

    while (P[i][j]) {
        j = P[i][j].value();
        S.push(j);
    }

    return S;
}

int main() {
    int n, m;
    cin >> n;
    cin >> m;
    Graph G(n);

    // Initialize every entry with value <inf>, except for an edge (i, i),
    // which have weight 0.
    for (size_t i = 0; i < n; i++) {
        G[i] = vector<Weight>(n, Inf);
        G[i][i] = 0;
    }

    for (size_t k = 0; k < m; k++) {
        size_t i, j;
        cin >> i;
        cin >> j;
        i--;
        j--;
        cin >> G[i][j];
        G[j][i] = G[i][j]; // G is not a directed graph.
    }

    Result *r = floydWarshall(G);
    cout << r->diameter << endl;
    cout << r->i + 1 << " " << r->j + 1 << endl;

    stack<Vertex> S = reconstructPath(r->P, r->i, r->j);
    cout << S.size() << endl;

    Vertex i = S.top();
    S.pop();
    cout << i + 1;
    while (!S.empty()) {
        i = S.top();
        S.pop();
        cout << " " << i + 1;
    }

    cout << endl;
    return 0;
}
