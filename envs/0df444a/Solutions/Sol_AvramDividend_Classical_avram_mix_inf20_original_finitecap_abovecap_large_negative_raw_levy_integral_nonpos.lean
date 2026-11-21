-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovecap_large_negative_raw_levy_integral_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:28:38.939976+00:00
-- url     : https://prove2.me/submissions/e64c7243-3236-4b8c-914c-609b8d956819

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℝ) (hy : C.toReal < y)
    (hI : Integrable (fun z : ℝ =>
      (if y + z ≤ C.toReal then w (y + z)
       else w C.toReal + (y + z - C.toReal)) -
        (w C.toReal + (y - C.toReal)))
      (X.ν.restrict (Iic (-1 : ℝ)))) :
    (∫ z in Iic (-1 : ℝ),
      (if y + z ≤ C.toReal then w (y + z)
       else w C.toReal + (y + z - C.toReal)) -
        (w C.toReal + (y - C.toReal)) ∂X.ν) ≤ 0 := by
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
  have hzneg : z < 0 := by
    have hz1 : z ≤ (-1 : ℝ) := hz
    linarith
  have h :=
    avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
      C hC hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy hzneg
  simpa [if_neg (not_le.mpr hy)] using h
