-- Prove2me | solution 1 for AvramDividend.Classical.atomless_from_weighted_measure_ac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:11:23.882182+00:00
-- url     : https://prove2.me/submissions/3ca6fb38-4a1a-4a24-82ab-6ce27ee5db55

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (μ : Measure ℝ) (hSupport : μ (Iio (0 : ℝ)) = 0)
    (hAtZero : μ {(0 : ℝ)} = 0)
    (hWeighted : (μ.withDensity (fun x : ℝ => ENNReal.ofReal x))
      ≪ (volume : Measure ℝ)) :
    ∀ x : ℝ, μ {x} = 0 := by
  intro x
  rcases lt_trichotomy x 0 with hneg | heq | hpos
  · have hsub : ({x} : Set ℝ) ⊆ Iio (0 : ℝ) := by
      intro y hy
      have hyx : y = x := by simpa using hy
      simpa only [mem_Iio, hyx] using hneg
    exact measure_mono_null hsub hSupport
  · simpa only [heq] using hAtZero
  · have hvol : (volume : Measure ℝ) {x} = 0 := by simp
    have hNull : (μ.withDensity (fun y : ℝ => ENNReal.ofReal y)) {x} = 0 :=
      hWeighted hvol
    have hwt : (μ.withDensity (fun y : ℝ => ENNReal.ofReal y)) {x} =
        ENNReal.ofReal x * μ {x} := by
      rw [withDensity_apply (fun y : ℝ => ENNReal.ofReal y)
        (measurableSet_singleton x)]
      exact lintegral_singleton _ x
    rw [hwt] at hNull
    have hxp : 0 < ENNReal.ofReal x := ENNReal.ofReal_pos.mpr hpos
    exact (mul_eq_zero.mp hNull).resolve_left (ne_of_gt hxp)
