-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb23_original_zero_or_positive_reserve_corrected_HJB_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:22:37.826598+00:00
-- url     : https://prove2.me/submissions/edafa10b-f629-4bbb-b96a-9611c91ac321

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (z : ℝ) (hz : 0 ≤ z) (hzC : ENNReal.ofReal z < C) :
    (if z = 0 then
      X.drift - q * w 0 +
        (∫ v in Iio (0 : ℝ), w ((0 : ℝ) + v) - w 0 ∂X.ν)
    else X.generator w z - q * w z) ≤ 0  := by
  by_cases hz0 : z = 0
  · subst z
    simpa using
      (avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
        X hX hBV hFinite q w C hC hw_cont hw0 hw_neg
        hw_smooth hw_gen hw_grad)
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    simpa [hz0] using (hw_gen z hzpos hzC).2
