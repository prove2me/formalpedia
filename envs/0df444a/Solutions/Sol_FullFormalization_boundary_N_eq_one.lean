-- Prove2me | solution 1 for FullFormalization.boundary_N_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:42:59.996463+00:00
-- url     : https://prove2.me/submissions/4227c6c4-6d89-4b68-b026-024a76db5b82

-- Generated from F:/20261008/FullFormalization\FullFormalization\NAGUpperBound.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.NAGUpperBound

  Source section 18: the dedicated exact certificate for the boundary case `N = 1`.

  Source (18.1):

      ‖r‖²/6 - F_1 = (1/2)(I_{⋆,0} + I_{0,1} + I_{⋆,1})
                     + (3/8) ‖g_0 - r/3‖² + (1/2) ‖g_1 - x_1/2‖²

  and the resulting bound `F_1 ≤ ‖r‖²/6`, which agrees with
  `2/(1² + 7·1 + 4) = 1/6`, so that the all-`N` formula has no gap at `N = 1`.

  The general `N ≥ 2` chain certificate does *not* cover `N = 1` (its index
  ranges are empty), which is exactly why the source gives this case
  separately.

  **Scalar-multiplication pitfall.**  In Lean a bare `(1 / 3) • r` elaborates
  the numeral `1 / 3` at type `ℕ` (where it is `0`), silently turning the term
  into `0 • r`.  Every scalar below is therefore written with an explicit `ℝ`
  ascription, e.g. `((1 : ℝ) / 3) • r`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_NAGUpperBound
import Definitions.Def_RationalNAG

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]







end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open FullFormalization in

theorem solution (r x1 g0 g1 : E) (F0 F1 : ℝ) (hx1 : x1 = r - g0) :
    ‖r‖ ^ 2 / 6 - F1
      = (1 / 2) * (Ival 0 F0 0 r 0 g0 + Ival F0 F1 r x1 g0 g1 + Ival 0 F1 0 x1 0 g1)
        + (3 / 8) * ‖g0 - ((1 : ℝ) / 3) • r‖ ^ 2
        + (1 / 2) * ‖g1 - ((1 : ℝ) / 2) • x1‖ ^ 2 := by
  subst hx1
  simp only [Ival, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_neg_left, inner_neg_right, inner_zero_left, inner_zero_right,
    real_inner_smul_left, real_inner_smul_right,
    norm_sub_sq_real, norm_add_sq_real, norm_smul, norm_neg, norm_zero,
    Real.norm_eq_abs, mul_pow, sq_abs, zero_sub, sub_zero,
    real_inner_self_eq_norm_sq,
    real_inner_comm r g0, real_inner_comm r g1, real_inner_comm g0 g1]
  ring
