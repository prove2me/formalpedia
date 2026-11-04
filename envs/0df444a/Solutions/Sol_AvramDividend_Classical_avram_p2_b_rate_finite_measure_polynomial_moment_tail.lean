-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_finite_measure_polynomial_moment_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:52:47.676158+00:00
-- url     : https://prove2.me/submissions/48416f13-67ae-4657-945a-60de12b8332b

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) (R : ℝ) (hR : 0 < R) (k : ℕ) :
    (ENNReal.ofReal R) ^ k * μ (Ici R) ≤
      ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ := by
  have hmeas : Measurable (fun z : ℝ => (ENNReal.ofReal z) ^ k) := by
    fun_prop
  have hsubset :
      Ici R ⊆ {z : ℝ | (ENNReal.ofReal R) ^ k ≤ (ENNReal.ofReal z) ^ k} := by
    intro z hz
    exact ENNReal.pow_le_pow_left (ENNReal.ofReal_le_ofReal hz)
  calc
    (ENNReal.ofReal R) ^ k * μ (Ici R) ≤
        (ENNReal.ofReal R) ^ k *
          μ {z : ℝ | (ENNReal.ofReal R) ^ k ≤ (ENNReal.ofReal z) ^ k} := by
      gcongr <;> exact measure_mono hsubset
    _ ≤ ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ := by
      simpa using MeasureTheory.mul_meas_ge_le_lintegral hmeas
        ((ENNReal.ofReal R) ^ k)
