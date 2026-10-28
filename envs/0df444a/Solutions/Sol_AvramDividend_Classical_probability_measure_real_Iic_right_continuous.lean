-- Prove2me | solution 1 for AvramDividend.Classical.probability_measure_real_Iic_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:46:35.587648+00:00
-- url     : https://prove2.me/submissions/f0a3e263-b0c5-47a4-b861-10427a1eacc2

import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Stieltjes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open ProbabilityTheory

theorem solution
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ContinuousWithinAt (fun y : ℝ => μ.real (Iic y)) (Ici x) x := by
  have hfun :
      (fun y : ℝ => μ.real (Iic y)) =
        (ProbabilityTheory.cdf μ : ℝ → ℝ) := by
    funext y
    exact (ProbabilityTheory.cdf_eq_real μ y).symm
  rw [hfun]
  exact (ProbabilityTheory.cdf μ).right_continuous x
