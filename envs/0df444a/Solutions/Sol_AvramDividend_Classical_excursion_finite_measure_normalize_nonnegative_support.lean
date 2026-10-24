-- Prove2me | solution 1 for AvramDividend.Classical.excursion_finite_measure_normalize_nonnegative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:17:40.628995+00:00
-- url     : https://prove2.me/submissions/9c5ef732-e8ec-4937-94f7-242333e8526d

import Mathlib.MeasureTheory.Measure.Prokhorov

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-!
Normalising a nonzero finite measure scales every set mass by
the inverse total mass. Consequently every null set remains null.
-/
theorem solution (μ : FiniteMeasure ℝ) (hμ : μ ≠ 0)
    (hsupport : μ (Iio (0 : ℝ)) = 0) :
    μ.normalize (Iio (0 : ℝ)) = 0 := by
  rw [FiniteMeasure.normalize_eq_of_nonzero μ hμ]
  simp only [hsupport, mul_zero]
