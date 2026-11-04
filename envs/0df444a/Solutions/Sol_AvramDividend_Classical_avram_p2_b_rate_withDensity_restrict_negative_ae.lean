-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_withDensity_restrict_negative_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:50:24.971598+00:00
-- url     : https://prove2.me/submissions/040978a2-f29b-42cf-bc86-2126789c4e36

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Restrict

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Restricting a Lévy measure to the negative half-line preserves negative support after any measurable density change. -/
theorem solution
    (ν : Measure ℝ) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    ∀ᵐ y ∂((ν.restrict (Set.Iio (0 : ℝ))).withDensity w), y < 0 := by
  have hrestrict : ∀ᵐ y ∂ν.restrict (Set.Iio (0 : ℝ)), y < 0 := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := ν) measurableSet_Iio] with y hy
    exact hy
  exact (MeasureTheory.ae_withDensity_iff
    (μ := ν.restrict (Set.Iio (0 : ℝ))) hw).2 (by
      filter_upwards [hrestrict] with y hy _
      exact hy)
