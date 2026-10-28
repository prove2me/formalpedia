-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.real_coercivity_le_uniform_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:29.352424+00:00
-- url     : https://prove2.me/submissions/ae73f899-6db5-49f7-aa03-cace11d06524

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity

noncomputable section
open FunctionalInequalities.Analysis
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- A finite real ceiling for the normalized coercivity expression. -/
theorem solution (A : ℝ) (n : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    Real.log A + (n : ℝ) * Real.log (max M 1) - M ≤
      Real.log A + (n : ℝ) * Real.log (2 * ((n : ℝ) + 1)) := by
  let d : ℝ := 2 * ((n : ℝ) + 1)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd1 : 1 ≤ d := by dsimp [d]; linarith
  have hd : 0 < d := zero_lt_one.trans_le hd1
  by_cases hs : M ≤ 1
  · rw [max_eq_right hs, Real.log_one, mul_zero]
    have hlog : 0 ≤ (n : ℝ) * Real.log d := mul_nonneg hn (Real.log_nonneg hd1)
    change Real.log A + 0 - M ≤ Real.log A + (n : ℝ) * Real.log d
    linarith
  · have hMp : 0 < M := by linarith
    have hq := Real.log_le_sub_one_of_pos (div_pos hMp hd)
    rw [Real.log_div hMp.ne' hd.ne'] at hq
    have hmul := mul_le_mul_of_nonneg_left hq hn
    have hfrac : (n : ℝ) * (M / d) ≤ M := by
      have hcancel : d * (M / d) = M := mul_div_cancel₀ _ hd.ne'
      have hqp : 0 ≤ M / d := div_nonneg hM hd.le
      dsimp [d] at hcancel
      nlinarith [mul_nonneg hn hqp]
    rw [max_eq_left (le_of_not_ge hs)]
    change Real.log A + (n : ℝ) * Real.log M - M ≤ Real.log A + (n : ℝ) * Real.log d
    nlinarith
