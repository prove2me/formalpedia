-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.inner_self_pos_of_norm_sub_one_lt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:34:24.582623+00:00
-- url     : https://prove2.me/submissions/89c6a8e5-c7a6-4bbc-9042-130c1233f4c3

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section S8CCompactToGeneral
open Filter Topology ProbabilityTheory FunctionalInequalities.Analysis
section OperatorHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- An operator with `‖A - 1‖ < 1` is strictly positive, hence a unit, when self-adjoint. -/
theorem solution
    [CompleteSpace E]
    {A : E →L[ℝ] E} (hA : ‖A - 1‖ < 1) {v : E} (hv : v ≠ 0) :
    0 < ⟪A v, v⟫ := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 : ⟪A v, v⟫ = ‖v‖ * ‖v‖ + ⟪(A - 1) v, v⟫ := by
    rw [sub_apply, one_apply_eq_self, inner_sub_left,
      real_inner_self_eq_norm_mul_norm]
    ring
  have h2 : ⟪(A - 1) v, v⟫ ≥ -(‖A - 1‖ * ‖v‖ * ‖v‖) := by
    have := real_inner_le_norm ((A - 1) v) (-v)
    rw [inner_neg_right, norm_neg] at this
    have h3 := ContinuousLinearMap.le_opNorm (A - 1) v
    nlinarith [norm_nonneg ((A - 1) v)]
  rw [h1]
  nlinarith [mul_pos hv' hv', norm_nonneg (A - 1)]
