-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_purejump_ubv_small_negative_band_rate_diverges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:20:37.541227+00:00
-- url     : https://prove2.me/submissions/e8e064d7-6cec-4bcf-b35e-a7200ea7b224

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
import Theorems.Thm_AvramDividend_Classical_negative_jump_small_band_tendsto_top
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_purejump_ubv_truncated_negative_rates_diverge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    Tendsto (fun δ : ℝ =>
      (X.ν (Ioo (-1 : ℝ) (-δ))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have hFar : X.ν (Iic (-1 : ℝ)) < ⊤ :=
    negative_jump_truncation_measure_finite X.ν X.ν_integrable 1 (by norm_num)
  have hFinite : ∀ δ : ℝ, 0 < δ → X.ν (Iio (-δ)) < ⊤ := by
    intro δ hδ
    have ht : X.ν (Iic (-δ)) < ⊤ :=
      negative_jump_truncation_measure_finite X.ν X.ν_integrable δ hδ
    exact lt_of_le_of_lt (measure_mono (by
      intro y hy
      change y < -δ at hy
      exact le_of_lt hy)) ht
  have hTail :=
    avram_f6_original_purejump_ubv_truncated_negative_rates_diverge X hBV hσ
  exact negative_jump_small_band_tendsto_top X.ν hFar hFinite hTail
