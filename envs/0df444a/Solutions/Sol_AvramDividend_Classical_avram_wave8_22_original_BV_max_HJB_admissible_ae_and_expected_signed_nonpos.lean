-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_max_HJB_admissible_ae_and_expected_signed_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T06:55:21.439619+00:00
-- url     : https://prove2.me/submissions/2ce2735b-e3ca-4d11-a51d-d34946205072

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_HJB_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_expected_nonpos
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original maximum-form BV HJB condition yields the genuine almost-sure and expected signed physical generator and Stieltjes corrections. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw_hjb : ∀ yy : ℝ, 0 < yy → ENNReal.ofReal yy < C →
X.GeneratorIntegrable w yy ∧ max (X.generator w yy - q * w yy) (1 - deriv w yy) = 0) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
(T : ℝ≥0) (A : Ω → Set ℝ≥0) (hAm : ∀ ω, MeasurableSet (A ω)) (hRegion : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω →
0 < Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧ ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) (hGInt : ∀ᵐ ω ∂P, IntegrableOn (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))) (A ω) (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
(B : Ω → Set ℝ) (hBm : ∀ ω, MeasurableSet (B ω)) (hDivRegion : ∀ᵐ ω ∂P, ∀ s, s ∈ B ω → 0 < riskProcess X x D s.toNNReal ω ∧
ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C) (hDivInt : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω))) (B ω) (dividendMeasure D ω))
(Gdrift Hdiv : Ω → ℝ) (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) (hHDef : ∀ᵐ ω ∂P, Hdiv ω = ∫ s in B ω, Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂(dividendMeasure D ω))
(hGI : Integrable Gdrift P) (hHI : Integrable Hdiv P) :
(∀ᵐ ω ∂P, Gdrift ω + Hdiv ω ≤ 0) ∧
  (∫ ω, Gdrift ω ∂P) + (∫ ω, Hdiv ω ∂P) ≤ 0 := by
  have hw_gen : ∀ yy : ℝ, 0 < yy → ENNReal.ofReal yy < C →
      X.GeneratorIntegrable w yy ∧ X.generator w yy - q * w yy ≤ 0 := by
    intro yy hy hyC
    obtain ⟨hInt, hMax⟩ := hw_hjb yy hy hyC
    refine ⟨hInt, ?_⟩
    have hL : X.generator w yy - q * w yy ≤
        max (X.generator w yy - q * w yy) (1 - deriv w yy) := le_max_left _ _
    rw [hMax] at hL
    exact hL
  have hw_grad : ∀ yy : ℝ, 0 < yy → ENNReal.ofReal yy < C →
      1 ≤ deriv w yy := by
    intro yy hy hyC
    have hMax := (hw_hjb yy hy hyC).2
    have hR : 1 - deriv w yy ≤
        max (X.generator w yy - q * w yy) (1 - deriv w yy) := le_max_right _ _
    rw [hMax] at hR
    linarith
  constructor
  · exact avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_HJB_nonpos
      X hBV q w C hw_gen hw_grad x D hD T A hAm hRegion hGInt
      B hBm hDivRegion hDivInt Gdrift Hdiv hGDef hHDef
  · exact avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_expected_nonpos
      X hBV q w C hw_gen hw_grad x D hD T A hAm hRegion hGInt
      B hBm hDivRegion hDivInt Gdrift Hdiv hGDef hHDef hGI hHI
