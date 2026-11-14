-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb24_original_source_zero_predividend_discounted_negative_mark_fibre_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:52:15.281457+00:00
-- url     : https://prove2.me/submissions/9a4e7cf3-ac75-48ab-8686-af1c15c95375

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (hw_neg : ∀ z < 0, w z = 0)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (t : ℝ≥0) (U : ℝ≥0 → ℝ)
    (hU : U t = 0) :
    (∫ z in Iio (0 : ℝ),
      Real.exp (-(q * (t : ℝ))) *
        (w (U t + z) - w (U t)) ∂X.ν) =
      -(Real.exp (-(q * (t : ℝ))) * w 0) *
        (X.ν (Iio (0 : ℝ))).toReal  := by
  simp only [hU, zero_add]
  rw [MeasureTheory.integral_const_mul]
  have hKernel :
      (∫ z in Iio (0 : ℝ), w z - w 0 ∂X.ν) =
        -(w 0) * (X.ν (Iio (0 : ℝ))).toReal := by
    simpa only [zero_add] using
      (avram_bvb22_original_zero_contact_negative_mark_kernel_exact
        X w hw_neg hFinite)
  rw [hKernel]
  ring
