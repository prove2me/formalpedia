-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb23_original_zero_contact_discounted_mark_kernel_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:19.891662+00:00
-- url     : https://prove2.me/submissions/877586ba-9cb5-4fc3-a3b3-3fdf9a959282

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_contact_negative_mark_kernel_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_neg : ∀ z < 0, w z = 0)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q T : ℝ) :
    (∫ t in Ioc (0 : ℝ) T,
      Real.exp (-(q * t)) *
        (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν)
      ∂(volume : Measure ℝ)) =
    (-(w 0) * (X.ν (Iio (0 : ℝ))).toReal) *
      (∫ t in Ioc (0 : ℝ) T,
        Real.exp (-(q * t)) ∂(volume : Measure ℝ))  := by
  rw [avram_bvb22_original_zero_contact_negative_mark_kernel_exact
    X w hw_neg hFinite]
  rw [MeasureTheory.integral_mul_const]
  ring
