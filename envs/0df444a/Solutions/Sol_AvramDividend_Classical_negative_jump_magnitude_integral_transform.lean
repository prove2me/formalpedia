-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_magnitude_integral_transform
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T10:18:40.630535+00:00
-- url     : https://prove2.me/submissions/14cf1491-9335-41ab-b979-c102e4910dae

import Mathlib

open MeasureTheory Set in open scoped NNReal ENNReal in
theorem solution (ν : Measure ℝ) (θ : ℝ) :
    (∫ z : ℝ≥0, (1 - Real.exp (-θ * (z : ℝ)))
      ∂(ν.map (fun y : ℝ => Real.toNNReal (-y)))) =
    ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂ν := by
  have hφ : Measurable (fun y : ℝ => Real.toNNReal (-y)) :=
    measurable_real_toNNReal.comp measurable_neg
  have hf : Continuous (fun z : ℝ≥0 => (1 - Real.exp (-θ * (z : ℝ)))) := by
    fun_prop
  rw [integral_map hφ.aemeasurable hf.aestronglyMeasurable,
    ← integral_indicator measurableSet_Iio]
  congr 1
  funext y
  by_cases hy : y < 0
  · rw [indicator_of_mem (show y ∈ Iio (0:ℝ) from hy)]
    rw [Real.coe_toNNReal _ (by linarith)]
    congr 2
    ring
  · rw [indicator_of_notMem (show y ∉ Iio (0:ℝ) from hy)]
    have hy' : 0 ≤ y := not_lt.mp hy
    rw [Real.toNNReal_of_nonpos (by linarith)]
    simp

