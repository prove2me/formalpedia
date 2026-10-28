-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.norm_sub_one_le_of_isPositive_mul_self_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:34:36.514022+00:00
-- url     : https://prove2.me/submissions/d38472b2-ed77-4d4b-8391-f3ff951e7b3d

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section S8CCompactToGeneral
open Filter Topology ProbabilityTheory FunctionalInequalities.Analysis
section OperatorHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A positive square root is at least as close to `1` as its square: `‖S - 1‖ ≤ ‖S² - 1‖`. -/
theorem solution
    [CompleteSpace E]
    {S Q : E →L[ℝ] E} (hS : S.IsPositive)
    (hQ : S * S = Q) : ‖S - 1‖ ≤ ‖Q - 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  set y := (S - 1) x with hy
  have hkey : ‖y‖ ≤ ‖(S + 1) y‖ := by
    have h1 : ‖y‖ * ‖y‖ ≤ ‖(S + 1) y‖ * ‖y‖ := by
      calc
        ‖y‖ * ‖y‖ = ⟪y, y⟫ := (real_inner_self_eq_norm_mul_norm y).symm
        _ ≤ ⟪S y, y⟫ + ⟪y, y⟫ := by
          have := hS.inner_nonneg_left y
          linarith
        _ = ⟪(S + 1) y, y⟫ := by
          rw [add_apply, one_apply_eq_self, inner_add_left]
        _ ≤ ‖(S + 1) y‖ * ‖y‖ := real_inner_le_norm _ _
    rcases (norm_nonneg y).eq_or_lt with h0 | h0
    · rw [← h0]; exact norm_nonneg _
    · exact le_of_mul_le_mul_right h1 h0
  have h2 : (S + 1) y = (Q - 1) x := by
    rw [hy, ← hQ]
    simp only [add_apply, sub_apply,
      one_apply_eq_self, mul_apply_eq_comp, map_sub]
    abel
  calc
    ‖(S - 1) x‖ = ‖y‖ := rfl
    _ ≤ ‖(S + 1) y‖ := hkey
    _ = ‖(Q - 1) x‖ := by rw [h2]
    _ ≤ ‖Q - 1‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
