-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_fullmark_integral_overshoot_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:07:19.793178+00:00
-- url     : https://prove2.me/submissions/0bd9db64-8a49-4ba1-9be6-941d0d0d2c89

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
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
    (V : ℝ → ℝ)
    (hV : ∀ t : ℝ, V t =
      if t ≤ C.toReal then w t
      else w C.toReal + (t - C.toReal))
    (y : ℝ) (hy : C.toReal < y)
    (hMI : Integrable (fun z : ℝ =>
      V (y + z) - V y - deriv V y * z)
      (X.ν.restrict (Iio (0 : ℝ))))
    (hOI : Integrable (fun z : ℝ => max 0 (-(y + z)))
      (X.ν.restrict (Iio (0 : ℝ)))) :
    (∫ z in Iio (0 : ℝ), V (y + z) - V y - deriv V y * z ∂X.ν) ≤
      (∫ z in Iio (0 : ℝ), max 0 (-(y + z)) ∂X.ν) := by
  have hEq : V = (fun t : ℝ =>
      if t ≤ C.toReal then w t
      else w C.toReal + (t - C.toReal)) := funext hV
  subst V
  apply integral_mono_ae hMI hOI
  filter_upwards [] with z
  exact avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
    C hC hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy
