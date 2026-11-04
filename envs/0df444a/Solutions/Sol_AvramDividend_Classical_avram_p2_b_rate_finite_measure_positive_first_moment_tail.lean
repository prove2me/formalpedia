-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_finite_measure_positive_first_moment_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:22:44.158279+00:00
-- url     : https://prove2.me/submissions/f95082eb-5d70-412b-846c-9e3c3d9263ae

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (μ : Measure ℝ) (R : ℝ) (hR : 0 < R) :
    ENNReal.ofReal R * μ (Ici R) ≤
      ∫⁻ z : ℝ, ENNReal.ofReal z ∂μ := by
  have hmeas : Measurable (fun z : ℝ => ENNReal.ofReal z) := by
    fun_prop
  have hsubset :
      Ici R ⊆ {z : ℝ | ENNReal.ofReal R ≤ ENNReal.ofReal z} := by
    intro z hz
    exact ENNReal.ofReal_le_ofReal hz
  calc
    ENNReal.ofReal R * μ (Ici R) ≤
        ENNReal.ofReal R *
          μ {z : ℝ | ENNReal.ofReal R ≤ ENNReal.ofReal z} := by
      gcongr <;> exact measure_mono hsubset
    _ ≤ ∫⁻ z : ℝ, ENNReal.ofReal z ∂μ := by
      simpa using MeasureTheory.mul_meas_ge_le_lintegral hmeas (ENNReal.ofReal R)
