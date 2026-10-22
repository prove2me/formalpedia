-- Prove2me | solution 1 for FullFormalization.probeAxis_lt_of_ne_zero_of_lt_opening
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:51:58.695847+00:00
-- url     : https://prove2.me/submissions/41e2d700-7b38-46ba-982e-27e14f352f97

-- Generated from F:/20261008/FullFormalization\FullFormalization\GridRefine.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.GridRefine

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 30
  (source lines 2561-2626), strategy 5 of section 21 (source line 2083).

  The source states, in lines 2565-2585:

      opening = min (2D+1, max(1, floor(N/2)))
      the opening probes contain 0, the other probes are fixed-amplitude points
      on the positive and negative coordinate axes; within the N budget the
      coordinate indices involved are < N; the axes of the refinement steps are
      `step mod D`, and since N < D = 2N+1 no high-index coordinate is reached
      inside the budget.

  The complete semantics are those of the frozen implementation that section 19
  authorises and section 35's cross-check script imports
  (`F:\Hardy_Run_2026-10-07_001215\workflow\hgcore\blackbox_algos.py`,
  `probe_list` and `_grid_then_refine`):

      points = [(0,)*dimension]
      for axis in range(dimension):
          for sign in (2, -2):
              point = [0]*dimension; point[axis] = sign; points.append(point)

      opening = min(len(points), max(1, spec.query_budget // 2))
      for index in range(opening):
          point = points[index]; answer = oracle.query(point)
          if best_value is None or answer["value"] < best_value: best = point
      size = 1
      for step in range(spec.query_budget - opening):
          axis = step % dimension
          sign = 1 if (step // dimension) % 2 == 0 else -1
          candidate = list(best); candidate[axis] += sign * size
          answer = oracle.query(candidate)
          if answer["value"] < best_value: best = candidate
          if (step + 1) % dimension == 0: size = size / 2
      oracle.finish(best)

  `probeList`, `probeAt`, `opening`, `refineAxis`, `refineSize`, `refineSign`,
  `refineCandidate`, `openQueries`, `openBest`, `refineLoop` and `run` below are
  that program, statement for statement:

  * `probeList D` is `[0] ++ [+2 e_0, -2 e_0, +2 e_1, -2 e_1, ...]`, so its
    length is `2*D+1` (`probeList_length`), and the index-to-axis/sign rule is
    `probeAxis` / `probeSign` (`probeAt_odd`, `probeAt_even`);
  * `opening N D = min (2*D+1) (max 1 (N/2))` is line 2565 verbatim, with the
    budget written `N` (`opening`, `opening_eq`);
  * the opening best is seeded by the first probe, which is the origin
    (`one_le_opening`: the opening is never empty), exactly as the frozen
    `best_value = None` makes the first query the initial incumbent — and the
    first query is the origin, so the fold from `0` below is that same program;
  * `refineAxis D s = s % D` is line 2579 verbatim;
  * `refineSign D s` uses `(s / D) % 2`, and `refineSize D s = (1/2)^(s / D)`,
    because the number of halvings completed before step `s` is exactly
    `s / D` (source line 2581: `if (step+1) % D == 0: size /= 2`);
  * the query count is exactly the budget (`run_queries_length`).

  All arithmetic below is in `ℕ` and `ℝ`; the source's "grid" is the coordinate
  grid of `EuclideanSpace ℝ (Fin D)`, and section 23's dimension `D = 2N+1`
  enters as `gridDim N`.

  A note on notation: every scalar multiple of a vector is written with an
  explicitly typed scalar (`(2 : ℝ) • v`, not `2 • v`), because a bare numeral
  in a `•` is elaborated at `ℕ` and would silently mean `nsmul`.
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_GridRefine
import Definitions.Def_PortfolioDefinitions
import Theorems.Thm_FullFormalization_opening_le_half

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

/-! ### The dimension of Theorem B (source (23.1)) -/









/-! ### The coordinate unit vectors and the probes -/









































/-! ### The opening (source lines 2565-2572) -/



















/-! ### The refinement loop (source lines 2579-2585) -/

























/-! ### The run -/

















namespace GridRefine











end GridRefine

end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false

open FullFormalization in

theorem solution (N D i : ℕ) (hN : 1 ≤ N) (hi0 : i ≠ 0)
    (hi : i < opening N D) : probeAxis i < N := by
  have h1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
  have h2 : i < max 1 (N / 2) := lt_of_lt_of_le hi (opening_le_half N D)
  have h3 : max 1 (N / 2) ≤ N := max_le hN (Nat.div_le_self N 2)
  have h4 : i < N := lt_of_lt_of_le h2 h3
  rw [probeAxis, Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
  omega
