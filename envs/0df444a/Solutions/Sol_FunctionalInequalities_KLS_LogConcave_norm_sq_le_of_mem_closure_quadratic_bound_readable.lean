-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.norm_sq_le_of_mem_closure_quadratic_bound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:38:36.253552+00:00
-- url     : https://prove2.me/submissions/ee3524b7-1605-4144-a58c-bd5614412166

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BrascampLieb

noncomputable section
open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open scoped ContDiff RealInnerProductSpace
section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- A continuous quadratic sublevel bound on a set controls the norm of any
point of its closure when that point is also the vector in the pairing. -/
theorem solution
    (z : H) {S : Set H} {C : ℝ} (hz : z ∈ closure S)
    (hbound : ∀ w ∈ S, 2 * ⟪z, w⟫ - ‖w‖ ^ 2 ≤ C) :
    ‖z‖ ^ 2 ≤ C := by
  have hcontinuous :
      Continuous (fun w : H => (2 : ℝ) * ⟪z, w⟫ - ‖w‖ ^ 2) :=
    (continuous_const.mul (continuous_const.inner continuous_id)).sub
      (continuous_id.norm.pow 2)
  have hclosed : IsClosed {w : H | 2 * ⟪z, w⟫ - ‖w‖ ^ 2 ≤ C} :=
    isClosed_le hcontinuous continuous_const
  have hclosure : closure S ⊆ {w : H | 2 * ⟪z, w⟫ - ‖w‖ ^ 2 ≤ C} :=
    closure_minimal (fun w hw => hbound w hw) hclosed
  have h := hclosure hz
  change 2 * ⟪z, z⟫ - ‖z‖ ^ 2 ≤ C at h
  rw [real_inner_self_eq_norm_sq] at h
  linarith only [h]
