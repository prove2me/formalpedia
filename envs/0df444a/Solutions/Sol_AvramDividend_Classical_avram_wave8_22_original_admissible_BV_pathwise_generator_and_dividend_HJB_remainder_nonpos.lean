-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_admissible_BV_pathwise_generator_and_dividend_HJB_remainder_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:22:14.543682+00:00
-- url     : https://prove2.me/submissions/e8a670bc-4c1d-45d2-9d73-dc27be9f3db1

import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_pathwise_generator_and_dividend_HJB_remainder_nonpos
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strictly interior physical BV generator and actual Stieltjes dividend corrections have nonpositive sum on each original path. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw_gen : ∀ yy : ℝ, 0 < yy → ENNReal.ofReal yy < C →
X.GeneratorIntegrable w yy ∧ X.generator w yy - q * w yy ≤ 0) (hw_grad : ∀ yy : ℝ, 0 < yy → ENNReal.ofReal yy < C → 1 ≤ deriv w yy) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
(T : ℝ≥0) (A : Ω → Set ℝ≥0) (hAm : ∀ ω, MeasurableSet (A ω)) (hRegion : ∀ ω t, t ∈ A ω →
0 < Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧ ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) (hGInt : ∀ ω, IntegrableOn (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))) (A ω) (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
(B : Ω → Set ℝ) (hBm : ∀ ω, MeasurableSet (B ω)) (hDivRegion : ∀ ω s, s ∈ B ω → 0 < riskProcess X x D s.toNNReal ω ∧
ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C) (hDivInt : ∀ ω, IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω))) (B ω) (dividendMeasure D ω))
(Gdrift Hdiv : Ω → ℝ) (hGDef : ∀ ω, Gdrift ω = ∫ t in A ω, Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) (hHDef : ∀ ω, Hdiv ω = ∫ s in B ω, Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂(dividendMeasure D ω)) :
∀ ω, Gdrift ω + Hdiv ω ≤ 0 := by
  have hDs : IsDividendStrategy 𝓕 D := hD.1.1
  exact avram_wave8_22_original_BV_pathwise_generator_and_dividend_HJB_remainder_nonpos
    X hBV q w C hw_gen hw_grad x D hDs T A hAm hRegion hGInt
    B hBm hDivRegion hDivInt Gdrift Hdiv hGDef hHDef
