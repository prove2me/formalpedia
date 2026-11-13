-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:48:20.922042+00:00
-- url     : https://prove2.me/submissions/9db8e1e5-3de7-4457-8ab6-e0273cf8daf9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_contact_negative_mark_kernel_exact
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
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    X.drift - q * w 0 +
      (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν) ≤ 0  := by
  have hbound :=
    avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
      X hX hBV hFinite q w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
  have hkernel :=
    avram_bvb22_original_zero_contact_negative_mark_kernel_exact
      X w hw_neg hFinite
  rw [hkernel]
  nlinarith
