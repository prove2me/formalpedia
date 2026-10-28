-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_downward_increment_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:20:43.674875+00:00
-- url     : https://prove2.me/submissions/ad0d2658-4a45-4ac3-bed9-5625422846cd

import Mathlib.Data.NNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal

/-- The number of negative decrements exceeding a threshold on any finite
observation grid is a measurable natural-number-valued path functional. -/
theorem solution
    (grid : Finset (ℝ≥0 × ℝ≥0)) (a : ℝ) :
    Measurable (fun f : ℝ≥0 → ℝ =>
      ∑ ij ∈ grid, if f ij.2 - f ij.1 < -a then (1 : ℕ) else 0) := by
  classical
  refine Finset.measurable_sum _ fun ij hij => ?_
  have hm1 : Measurable (fun f : ℝ≥0 → ℝ => f ij.1) :=
    measurable_pi_apply _
  have hm2 : Measurable (fun f : ℝ≥0 → ℝ => f ij.2) :=
    measurable_pi_apply _
  have hs : MeasurableSet
      {f : ℝ≥0 → ℝ | f ij.2 - f ij.1 < -a} := by
    change MeasurableSet
      ((fun f : ℝ≥0 → ℝ => f ij.2 - f ij.1) ⁻¹' Iio (-a))
    exact (isOpen_Iio.measurableSet).preimage (hm2.sub hm1)
  exact Measurable.ite hs measurable_const measurable_const
