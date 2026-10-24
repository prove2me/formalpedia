-- Prove2me | solution 1 for AvramDividend.Classical.excursion_probability_weak_limit_nonnegative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:53:49.912947+00:00
-- url     : https://prove2.me/submissions/dbe3d8f5-aacb-48cb-ae12-9cba8cc5f220

import Mathlib.MeasureTheory.Measure.Portmanteau

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology

/-!
The open negative half-line cannot acquire positive mass in a weak
limit when every approximating probability measure assigns it zero mass.
-/
theorem solution
    (ν : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hν : Tendsto ν atTop (𝓝 μ))
    (hsupport : ∀ n : ℕ, (ν n : Measure ℝ) (Iio (0 : ℝ)) = 0) :
    (μ : Measure ℝ) (Iio (0 : ℝ)) = 0 := by
  have hport :
      (μ : Measure ℝ) (Iio (0 : ℝ)) ≤
        Filter.liminf (fun n : ℕ => (ν n : Measure ℝ) (Iio (0 : ℝ))) atTop :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν isOpen_Iio
  have hle : (μ : Measure ℝ) (Iio (0 : ℝ)) ≤ 0 := by
    simpa only [hsupport, Filter.liminf_const] using hport
  exact le_antisymm hle zero_le
