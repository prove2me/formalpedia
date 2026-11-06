-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_localized_weighted_generator_drift_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:54:55.615544+00:00
-- url     : https://prove2.me/submissions/8bb1f11a-b2c2-49e4-b14a-d979df6e2842

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_interior_jump_discount_drift_cover
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x))
    (μ : Measure ℝ) (Y g : ℝ → ℝ)
    (hg : ∀ᵐ t ∂μ, 0 ≤ g t)
    (hY : ∀ᵐ t ∂μ, 0 < Y t ∧ ENNReal.ofReal (Y t) < C)
    (hIntD : Integrable (fun t => g t * X.drift) μ)
    (hIntG : Integrable (fun t => g t *
      (q * w (Y t) - ∫ z in Iio (0 : ℝ),
        w (Y t + z) - w (Y t) ∂X.ν)) μ) :
    (∫ t, g t * X.drift ∂μ) ≤
      ∫ t, g t * (q * w (Y t) -
        ∫ z in Iio (0 : ℝ),
          w (Y t + z) - w (Y t) ∂X.ν) ∂μ := by
  have hpoint : ∀ᵐ t ∂μ,
      g t * X.drift ≤ g t * (q * w (Y t) -
        ∫ z in Iio (0 : ℝ),
          w (Y t + z) - w (Y t) ∂X.ν) := by
    filter_upwards [hg, hY] with t hgt ht
    have hCover :=
      avram_wave7_17_original_BV_complement_interior_jump_discount_drift_cover
        X hX hBV q hq w C hC hw_cont hw0 hw_smooth
        hw_gen hw_grad x hx hxc D hD T hT hEnvelope
        (Y t) ht.1 ht.2
    exact mul_le_mul_of_nonneg_left hCover.2.2 hgt
  exact integral_mono_ae hIntD hIntG hpoint
