-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_probability_real_law_ext_of_strict_CDF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T09:34:41.405478+00:00
-- url     : https://prove2.me/submissions/a163eb9f-9b69-4318-8cad-d37a5147c708

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- A probability law on the reals is determined by all strict lower-ray masses. -/
theorem solution
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ a : ℝ, μ (Iio a) = ν (Iio a)) : μ = ν := by
  apply Measure.ext_of_Ici μ ν
  intro a
  have hμ : μ (Ici a) = 1 - μ (Iio a) := by
    simpa only [Set.compl_Iio, measure_univ] using
      (measure_compl (μ := μ) (measurableSet_Iio : MeasurableSet (Iio a))
        (measure_ne_top μ (Iio a)))
  have hν : ν (Ici a) = 1 - ν (Iio a) := by
    simpa only [Set.compl_Iio, measure_univ] using
      (measure_compl (μ := ν) (measurableSet_Iio : MeasurableSet (Iio a))
        (measure_ne_top ν (Iio a)))
  rw [hμ, hν, h a]
