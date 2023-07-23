#include <stdio.h>
#include <assert.h>

#ifndef N
#define N 3
#endif

#ifndef B
#define B 10
#endif

int main(void) {
  int table[B][N+1];

  // Setup constraints for the contents of the table...
  for (int i = 0; i < B; ++i) {
    int y = 1;
    int x = 1;

    for (int j = 0; j < N; ++j) {
      x *= i;
    }

    for (int j = 0; j < N+1; ++j) {
      __CPROVER_assume(table[i][j] == x - i * y);
      y *= B;
    }
  }

  // This will end up being the solution.
  int soln[N+1];

  // Disallow the solver from finding solutions that we've already found.
  // These are the solutions for N=3, B=10.
#define NDISALLOWED 6
  int disallowed[NDISALLOWED][N+1] = {
    {0, 0, 0, 0},
    {1, 0, 0, 0},
    {7, 0, 4, 0},
    {0, 7, 3, 0},
    {1, 7, 3, 0},
    {3, 5, 1, 0},
  };

  // The number of solutions to exclude. You can set this to e.g.
  // 2 to get some example solutions.
#ifndef CHECK_SOLUTIONS
#define CHECK_SOLUTIONS 6
#endif

  // Setup the constraints to prevent the solver from finding a disallowed
  // solution.
  for (int i = 0; i < CHECK_SOLUTIONS; ++i) {
    int is_same = 1;
    for (int j = 0; j < N+1; ++j) {
      int w = soln[j];
      int v = disallowed[i][j];
      is_same &= (v == w);
    }
    __CPROVER_assume(!is_same);
  }

  // Setup the constraints that the solution must sum to 0.
  int z = 0;

  for (int i = N; i >= 0; --i) {
    __CPROVER_assume(soln[i] < 10);
    __CPROVER_assume(soln[i] >= 0);

    int idx = soln[i];
    int w = table[idx][i];

    z += w;
  }

  assert(z != 0);
}
