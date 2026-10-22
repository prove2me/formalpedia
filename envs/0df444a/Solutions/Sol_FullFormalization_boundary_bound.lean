-- Prove2me | solution 1 for FullFormalization.boundary_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T06:02:37.808072+00:00
-- url     : https://prove2.me/submissions/1c9a4c06-77dc-4e87-a68d-717b3c6b5981

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
import Theorems.Thm_FullFormalization_Ival_nonneg
import Theorems.Thm_FullFormalization_boundary_N_eq_one
import Theorems.Thm_FullFormalization_convexOn_le_gradient
import Theorems.Thm_FullFormalization_descent_lemma
import Theorems.Thm_FullFormalization_differentiable_inner_const
import Theorems.Thm_FullFormalization_gradient_inner_const
import Theorems.Thm_FullFormalization_gradient_sub
import Theorems.Thm_FullFormalization_gradient_sub_inner
import Theorems.Thm_FullFormalization_mom_zero
import Theorems.Thm_FullFormalization_nagX_succ
import Theorems.Thm_FullFormalization_nagX_zero
import Theorems.Thm_FullFormalization_nagY_succ
import Theorems.Thm_FullFormalization_nagY_succ_one
import Theorems.Thm_FullFormalization_nagY_zero

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

theorem solution {f : E → ℝ} (hf : NormalizedAtZero f) (r : E) :
    f (nagX f 1 r 1) - f 0 ≤ ‖r‖ ^ 2 / 6 := by
  have hx1 : nagX f 1 r 1 = r - ∇ f r := by
    simp only [nagX_succ, nagY_succ_one, nagY_zero, nagX_zero, mom_zero, zero_smul, add_zero]
  have key := boundary_N_eq_one r (nagX f 1 r 1) (∇ f r) (∇ f (nagX f 1 r 1))
    (f r) (f (nagX f 1 r 1)) hx1
  have h1 : 0 ≤ Ival 0 (f r) 0 r 0 (∇ f r) := by
    have := Ival_nonneg hf.convex hf.differentiable hf.smooth (0 : E) r
    simpa [hf.value_at_zero, hf.grad_at_zero] using this
  have h2 : 0 ≤ Ival (f r) (f (nagX f 1 r 1)) r (nagX f 1 r 1) (∇ f r)
      (∇ f (nagX f 1 r 1)) :=
    Ival_nonneg hf.convex hf.differentiable hf.smooth r (nagX f 1 r 1)
  have h3 : 0 ≤ Ival 0 (f (nagX f 1 r 1)) 0 (nagX f 1 r 1) 0 (∇ f (nagX f 1 r 1)) := by
    have := Ival_nonneg hf.convex hf.differentiable hf.smooth (0 : E) (nagX f 1 r 1)
    simpa [hf.value_at_zero, hf.grad_at_zero] using this
  have hsum1 : 0 ≤ Ival 0 (f r) 0 r 0 (∇ f r)
      + Ival (f r) (f (nagX f 1 r 1)) r (nagX f 1 r 1) (∇ f r) (∇ f (nagX f 1 r 1))
      + Ival 0 (f (nagX f 1 r 1)) 0 (nagX f 1 r 1) 0 (∇ f (nagX f 1 r 1)) := by linarith
  have hsum2 : 0 ≤ (3 / 8) * ‖(∇ f r) - ((1 : ℝ) / 3) • r‖ ^ 2
      + (1 / 2) * ‖(∇ f (nagX f 1 r 1)) - ((1 : ℝ) / 2) • (nagX f 1 r 1)‖ ^ 2 := by positivity
  rw [hf.value_at_zero]
  linarith [key, hsum1, hsum2]
