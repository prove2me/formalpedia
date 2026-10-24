-- Prove2me | solution 1 for AvramDividend.Classical.excursion_rescaled_probability_support_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:23:40.156886+00:00
-- url     : https://prove2.me/submissions/501f950e-3836-4e04-b531-aa7d1d799e4b

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-!
Rescaling a probability measure by a finite nonnegative scalar
preserves a null negative half-line and gives the prescribed
total mass.
-/
theorem solution
    (P : ProbabilityMeasure ℝ) (c : NNReal)
    (hP : (P : Measure ℝ) (Iio (0 : ℝ)) = 0) :
    ((c • P.toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ) (Iio (0 : ℝ)) = 0 ∧
    ((c • P.toFiniteMeasure : FiniteMeasure ℝ) : Measure ℝ) Set.univ =
      (c : ENNReal) := by
  constructor
  · simpa [FiniteMeasure.toMeasure_smul, hP]
  · simp [FiniteMeasure.toMeasure_smul]
