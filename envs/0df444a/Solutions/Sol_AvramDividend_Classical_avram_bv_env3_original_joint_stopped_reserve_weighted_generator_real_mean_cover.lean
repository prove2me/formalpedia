-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_joint_stopped_reserve_weighted_generator_real_mean_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:03:17.858237+00:00
-- url     : https://prove2.me/submissions/b53bd141-e35b-447a-bc2a-9a3227541d04

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
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hEnvelope : ¬ (x + T * X.drift ≤ w x))
    (μ : Measure (ℝ≥0 × Ω)) (g : ℝ≥0 × Ω → ℝ)
    (hg : ∀ᵐ p ∂μ, 0 ≤ g p)
    (hInterior : ∀ᵐ p ∂μ,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (hIntD : Integrable (fun p => g p * X.drift) μ)
    (hIntG : Integrable (fun p => g p *
      (q * w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
        ∫ z in Iio (0 : ℝ),
          w ((Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) + z) -
            w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν)) μ) :
    (∫ p, g p * X.drift ∂μ) ≤
      ∫ p, g p * (q * w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
        ∫ z in Iio (0 : ℝ),
          w ((Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) + z) -
            w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν) ∂μ := by
  have hpoint : ∀ᵐ p ∂μ,
      g p * X.drift ≤ g p * (q * w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
        ∫ z in Iio (0 : ℝ),
          w ((Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) + z) -
            w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν) := by
    filter_upwards [hg, hInterior] with p hgp hp
    have hCover :=
      avram_wave7_17_original_BV_complement_interior_jump_discount_drift_cover
        X hX hBV q hq w C hC hw_cont hw0 hw_smooth
        hw_gen hw_grad x hx hxc D hD T hT hEnvelope
        (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) hp.1 hp.2
    exact mul_le_mul_of_nonneg_left hCover.2.2 hgp
  exact integral_mono_ae hIntD hIntG hpoint
