-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.exists_bound_of_log_lower_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:30.846607+00:00
-- url     : https://prove2.me/submissions/bc3aab1d-77ad-4cf2-9b09-323c54a3b170

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity

noncomputable section
open FunctionalInequalities.Analysis
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
/-- Elementary logarithmic coercivity. The bound is constructed from A,n,b;
no asymptotic growth or desired integral bound is passed as a premise. -/
theorem solution (A : ℝ) (n : ℕ) (b : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℝ, 0 ≤ M →
      b ≤ Real.log A + (n : ℝ) * Real.log (max M 1) - M → M ≤ B := by
  let d : ℝ := 2 * ((n : ℝ) + 1)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < d := by dsimp [d]; positivity
  let B : ℝ := max 1 (2 * (Real.log A + (n : ℝ) * Real.log d - b))
  refine ⟨B, zero_le_one.trans (le_max_left _ _), ?_⟩
  intro M hM hb
  by_cases hsmall : M ≤ 1
  · exact hsmall.trans (le_max_left _ _)
  have hMpos : 0 < M := by linarith
  have hq := Real.log_le_sub_one_of_pos (div_pos hMpos hd)
  rw [Real.log_div hMpos.ne' hd.ne'] at hq
  have hmul := mul_le_mul_of_nonneg_left hq hn
  have hfraction : (n : ℝ) * (M / d) ≤ M / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hcancel : d * (M / d) = M := mul_div_cancel₀ _ hd.ne'
    have hqpos : 0 ≤ M / d := div_nonneg hM hd.le
    dsimp [d] at hcancel
    nlinarith
  rw [max_eq_left (le_of_not_ge hsmall)] at hb
  have hB : M ≤ 2 * (Real.log A + (n : ℝ) * Real.log d - b) := by nlinarith
  exact hB.trans (le_max_right _ _)
