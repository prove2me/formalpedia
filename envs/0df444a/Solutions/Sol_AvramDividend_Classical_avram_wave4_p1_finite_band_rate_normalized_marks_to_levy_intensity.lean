-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_finite_band_rate_normalized_marks_to_levy_intensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:33:54.675983+00:00
-- url     : https://prove2.me/submissions/346bde0f-62f7-4305-a19f-38d18bf07aa4

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {E : Type*} [MeasurableSpace E]
    (ν ρ : Measure E) [IsProbabilityMeasure ρ]
    (rate : ℝ≥0∞) (hrate : rate < ∞) (hν : ν = rate • ρ)
    (f : E → ℝ) (hf : Integrable f ρ)
    (t : ℝ) (ht : 0 ≤ t) :
    (t * rate.toReal) * ∫ z, f z ∂ρ =
      t * ∫ z, f z ∂ν := by
  rw [hν, MeasureTheory.integral_smul_measure]
  simp only [smul_eq_mul]
  ring
