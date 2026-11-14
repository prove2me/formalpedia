-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.entropy_is_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:44:48.566064+00:00
-- url     : https://prove2.me/submissions/5431ef9a-e97a-4f70-8112-7d30da2fb497

import Definitions.Def_CountingLLL_ReciprocalTest

open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem uniformLaw_probability (n : ℕ) : IsProbabilityMeasure (uniformLaw n) := by
  constructor
  simp [uniformLaw, Measure.smul_apply, Measure.count_apply]
  apply ENNReal.inv_mul_cancel <;> simp


theorem oracleLaw_probability (B : ℝ≥0∞) (hB : B ≤ 1) : IsProbabilityMeasure (oracleLaw B) := by
  constructor
  simp only [oracleLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [add_comm, tsub_add_cancel_of_le hB]

theorem fairLaw_probability : IsProbabilityMeasure fairLaw := by
  constructor
  simp only [fairLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← two_mul]
  rw [one_div]
  exact ENNReal.mul_inv_cancel (by norm_num) (by simp)


theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) : IsProbabilityMeasure (entropyLaw B) := by
  letI : IsProbabilityMeasure (oracleLaw B) := oracleLaw_probability B hB
  letI : IsProbabilityMeasure fairLaw := fairLaw_probability
  letI (a : ℕ × ℕ) : IsProbabilityMeasure (uniformLaw a.1) := uniformLaw_probability a.1
  unfold entropyLaw
  infer_instance
