-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.opNorm_le_of_inner_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:34:56.703957+00:00
-- url     : https://prove2.me/submissions/d4c65c51-c75b-44b7-a8e3-7e5cd6b2cd85

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
section S8CCompactToGeneral
open Filter Topology ProbabilityTheory FunctionalInequalities.Analysis
section OperatorHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- An operator represented by a bilinear form is bounded by the form's norm. -/
theorem solution
    [CompleteSpace E]
    {A : E →L[ℝ] E}
    {κ : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ}
    (h : ∀ u v : E, ⟪A u, v⟫ = κ ![u, v]) : ‖A‖ ≤ ‖κ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  have h1 : ‖A u‖ * ‖A u‖ ≤ (‖κ‖ * ‖u‖) * ‖A u‖ := by
    calc
      ‖A u‖ * ‖A u‖ = ⟪A u, A u⟫ := (real_inner_self_eq_norm_mul_norm _).symm
      _ = κ ![u, A u] := h u (A u)
      _ ≤ ‖κ ![u, A u]‖ := le_abs_self _
      _ ≤ ‖κ‖ * ∏ i, ‖(![u, A u] : Fin 2 → E) i‖ := κ.le_opNorm _
      _ = (‖κ‖ * ‖u‖) * ‖A u‖ := by
        rw [Fin.prod_univ_two]
        simp [mul_assoc]
  rcases (norm_nonneg (A u)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · exact le_of_mul_le_mul_right h1 h0
