-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_expMeasure_strict_positive_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:21:55.2742+00:00
-- url     : https://prove2.me/submissions/4cea85f9-c277-4064-9ac0-db8409d386d1

import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem solution (p n : ℝ) (hp : 0 < p) (hn : 0 ≤ n) :
    0 < expMeasure p (Ioi n) := by
  let μ : Measure ℝ := expMeasure p
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_expMeasure hp
  have hsum : μ (Iic n) + μ (Ioi n) = 1 := by
    have hm := measure_add_measure_compl
      (μ := μ) (measurableSet_Iic : MeasurableSet (Iic n))
    simpa [Set.compl_Iic] using hm
  by_contra h
  have hzero : μ (Ioi n) = 0 :=
    le_antisymm (le_of_not_gt h) (bot_le : (0 : ℝ≥0∞) ≤ μ (Ioi n))
  have hleft : μ (Iic n) = 1 := by
    simpa [hzero] using hsum
  have hcdf : cdf μ n = 1 := by
    rw [cdf_eq_real]
    simp [Measure.real_def, hleft]
  have hformula := cdf_expMeasure_eq hp n
  rw [if_pos hn] at hformula
  dsimp [μ] at hcdf
  linarith [Real.exp_pos (-(p * n))]
