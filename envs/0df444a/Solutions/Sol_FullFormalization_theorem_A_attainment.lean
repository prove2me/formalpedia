-- Prove2me | solution 1 for FullFormalization.theorem_A_attainment
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T06:53:16.972697+00:00
-- url     : https://prove2.me/submissions/10a80240-7279-4d59-b1fc-cacb6eb0b0cb

-- Generated from F:/20261008/FullFormalization\FullFormalization\TheoremA.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.TheoremA

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`.
  Theorem A (source lines 17-56, boxed at line 3002) assembled from the pieces
  that are already verified elsewhere in this development.

  The three layers:

  * `nag_upper_bound_normalized` — (1.1)/(17.1) in the normalised setting
    `L = 1`, `x⋆ = 0`, `f⋆ = 0`, where the initial point is `r` and the radius is
    `‖r‖`: `F_N - f⋆ = F_N ≤ τ_N ‖r‖²`.  For `N ≥ 2` this is the master
    certificate (7.1) of section 12 — `CertificateIdentities` (9.1), (10.1),
    (11.1), (11.2) fed into `MasterCertificate.telescope` — combined with the
    nonnegativity of the interpolation residual (2.2), of the square terms
    (sections 14-16) and of the weights (section 13).  For `N = 1` it is the
    dedicated certificate (18.1) of section 18 (`NAGUpperBound.boundary_bound`),
    whose value `1/6` is exactly `τ_1`, so the two branches join without gap.

  * `theorem_A_upper` — the general `L, R` form (19.1)/(32.1).  Given an
    admissible `f` with optimiser `x⋆` and `‖x₀ - x⋆‖ ≤ R`, the normalised
    function is `f_N y = (f (x⋆ + R y) - f⋆)/(L R²)`, which is
    `NormalizedAtZero`; `Scaling.gradient_scaled` and `Scaling.differentiable_scaled`
    (with the local `gradient_normalized`/`gradient_const_add`) show that both
    NAG trajectories are related by `x_k = x⋆ + R · x_k^N` (proved directly, as
    in `Scaling.nag_pair_scaled`, but starting from the general `x₀`), and
    `nag_upper_bound_normalized` applied to `f_N` then gives the bound.

  * `theorem_A_attainment` / `theorem_A` / `theorem_A_sup` — the equality case of
    section 20: the one-dimensional Huber function (`Huber1D.huber_attainment`)
    is `NormalizedAtZero` and attains `τ_N` exactly.  **The supremum claim is
    stated in both forms**: `theorem_A_sup` is the literal `sSup` statement, and
    `theorem_A` is the equivalent pair "every admissible function satisfies the
    upper bound" ∧ "some admissible function attains it".  The pair form is the
    one used to *prove* the supremum (upper half + attained value), and the two
    forms are equivalent, so neither weakens the mathematics.
    (`theorem_A_attainment_admissible` records the same attainment in the
    source's own `Admissible`-class vocabulary.)

  **Scalar-multiplication pitfall** (hit three times earlier in this project):
  a bare `(1/2) • v` elaborates the numeral at type `ℕ`.  Every scalar in this
  file is written with an explicit `ℝ` ascription, e.g. `((1 : ℝ) / 2) • v`.

  Nothing is postulated: no `sorry`, `admit`, `axiom` or `unsafe`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_Huber1D
import Definitions.Def_NAGUpperBound
import Definitions.Def_Positivity
import Definitions.Def_RationalNAG
import Definitions.Def_Scaling
import Definitions.Def_TheoremA
import Theorems.Thm_FullFormalization_d_mono
import Theorems.Thm_FullFormalization_d_nonneg
import Theorems.Thm_FullFormalization_d_one
import Theorems.Thm_FullFormalization_d_sub_pred
import Theorems.Thm_FullFormalization_d_succ_sub
import Theorems.Thm_FullFormalization_d_zero
import Theorems.Thm_FullFormalization_deriv_huber
import Theorems.Thm_FullFormalization_hasDerivAt_huber
import Theorems.Thm_FullFormalization_hasDerivAt_huber_pos
import Theorems.Thm_FullFormalization_hasDerivAt_linear
import Theorems.Thm_FullFormalization_hasDerivAt_neglinear
import Theorems.Thm_FullFormalization_hasDerivAt_sq_div_two
import Theorems.Thm_FullFormalization_huberC_le_traj
import Theorems.Thm_FullFormalization_huberC_mul
import Theorems.Thm_FullFormalization_huberC_pos
import Theorems.Thm_FullFormalization_huberC_sq
import Theorems.Thm_FullFormalization_huberC_sub
import Theorems.Thm_FullFormalization_huberClamp_lipschitz
import Theorems.Thm_FullFormalization_huberClamp_mono
import Theorems.Thm_FullFormalization_huberClamp_of_abs_lt
import Theorems.Thm_FullFormalization_huberClamp_of_c_le
import Theorems.Thm_FullFormalization_huberClamp_of_le_neg
import Theorems.Thm_FullFormalization_huberE_succ
import Theorems.Thm_FullFormalization_huberE_zero
import Theorems.Thm_FullFormalization_huber_algebra
import Theorems.Thm_FullFormalization_huber_convex
import Theorems.Thm_FullFormalization_huber_diff
import Theorems.Thm_FullFormalization_huber_final_value
import Theorems.Thm_FullFormalization_huber_in_linear_region
import Theorems.Thm_FullFormalization_huber_min
import Theorems.Thm_FullFormalization_huber_nonneg
import Theorems.Thm_FullFormalization_huber_of_abs_le
import Theorems.Thm_FullFormalization_huber_of_c_le
import Theorems.Thm_FullFormalization_huber_of_le_neg
import Theorems.Thm_FullFormalization_huber_smooth
import Theorems.Thm_FullFormalization_huber_traj
import Theorems.Thm_FullFormalization_huber_traj_pair
import Theorems.Thm_FullFormalization_huber_zero
import Theorems.Thm_FullFormalization_huber_zero_fun
import Theorems.Thm_FullFormalization_mom_zero
import Theorems.Thm_FullFormalization_nagX_succ
import Theorems.Thm_FullFormalization_nagX_succ_prime
import Theorems.Thm_FullFormalization_nagY_succ
import Theorems.Thm_FullFormalization_nagY_succ_one
import Theorems.Thm_FullFormalization_tau_eq_inv
import Theorems.Thm_FullFormalization_two_d_add_one

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### (1.1) / (17.1): the upper bound in the normalised setting -/



/-! ### Auxiliary gradient lemmas for the scaling (32.1) -/











/-! ### (19.1): the general `L, R` upper bound -/



/-! ### (20.4): the matching lower bound, and Theorem A -/











end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open FullFormalization in

theorem solution (N : ℕ) (hN : 1 ≤ N) {R : ℝ} (hR : 0 < R) :
    ∃ f : ℝ → ℝ, NormalizedAtZero f ∧
      (f (nagX f 1 R N) - f 0) / R ^ 2 = tau N := by
  have hc : 0 ≤ huberC N R := (huberC_pos hR).le
  refine ⟨huber (huberC N R), ⟨huber_convex hc, huber_diff hc, ?_, huber_zero hc, ?_,
    fun x => huber_min hc x⟩, huber_final_value N hR⟩
  · intro a b
    have hs := huber_smooth hc a b
    simpa [gradient_eq_deriv', one_mul] using hs
  · rw [gradient_eq_deriv', deriv_huber hc, huberClamp,
      min_eq_right (by linarith : (0 : ℝ) ≤ huberC N R),
      max_eq_right (by linarith : -huberC N R ≤ 0)]
