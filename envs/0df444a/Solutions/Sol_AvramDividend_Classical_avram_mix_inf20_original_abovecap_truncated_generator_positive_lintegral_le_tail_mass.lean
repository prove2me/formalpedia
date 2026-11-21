-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_abovecap_truncated_generator_positive_lintegral_le_tail_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:10:28.226795+00:00
-- url     : https://prove2.me/submissions/d954575f-61d0-4976-8565-dea31e49f223

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_abovecap_true_truncated_jump_positive_tail_unit_domination
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ y : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hδcap : δ ≤ C.toReal) (hy : C.toReal < y) :
    (∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal
        (SpectrallyNegativeLevy.generatorIntegrand
          (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
          y z) ∂X.ν) ≤
      (X.ν.restrict (Iio (0 : ℝ))) (Iic (-δ)) := by
  have hb : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ENNReal.ofReal
        (SpectrallyNegativeLevy.generatorIntegrand
          (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
          y z) ≤
      (Iic (-δ)).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) z := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
    have hmark :=
      avram_mix_inf20_original_abovecap_true_truncated_jump_positive_tail_unit_domination
        C hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad
        δ y z hδ hδone hδcap hy hz
    have hreal := ENNReal.ofReal_le_ofReal hmark
    by_cases htail : z ≤ -δ
    · simpa [Set.indicator, htail] using hreal
    · simpa [Set.indicator, htail] using hreal
  calc
    (∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal (SpectrallyNegativeLevy.generatorIntegrand
        (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
        y z) ∂X.ν)
      ≤ ∫⁻ z, (Iic (-δ)).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) z
            ∂(X.ν.restrict (Iio (0 : ℝ))) := lintegral_mono_ae hb
    _ = (X.ν.restrict (Iio (0 : ℝ))) (Iic (-δ)) :=
        lintegral_indicator_one measurableSet_Iic
