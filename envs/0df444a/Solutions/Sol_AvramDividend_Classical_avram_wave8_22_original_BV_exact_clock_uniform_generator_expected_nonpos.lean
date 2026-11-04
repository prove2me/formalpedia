-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_exact_clock_uniform_generator_expected_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:36:40.355628+00:00
-- url     : https://prove2.me/submissions/6a3aa05c-cada-46ff-9102-c200917131fa

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_uniform_capped_generator_expected_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_real_to_nnreal_finite_horizon_clock
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The genuine finite original time clock removes the separately postulated clock mass assumption from the expected stopped HJB sign theorem. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (T : ℝ≥0) (μT : Measure ℝ≥0) [SFinite μT]
  (hTime : μT = (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
  (A : Ω → Set ℝ≥0) (hAm : ∀ ω, MeasurableSet (A ω))
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ t ω, K t ω =
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t)))
  (F : (ℝ≥0 × Ω) → ℝ)
  (hF : ∀ p, F p = if p.1 ∈ A p.2 then K p.1 p.2 else 0)
  (hASet : MeasurableSet {p : ℝ≥0 × Ω | p.1 ∈ A p.2})
  (hKmeas : Measurable (fun p : ℝ≥0 × Ω => K p.1 p.2))
  (B : ℝ) (hBnonneg : 0 ≤ B)
  (hUniform : ∀ᵐ p ∂(μT.prod P), ‖F p‖ ≤ B)
  (Gdrift : Ω → ℝ)
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, K t ω ∂μT)
  (C : ℝ≥0∞)
  (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧
    max (X.generator w y - q * w y) (1 - deriv w y) = 0)
  (hRegion : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω →
    0 < Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
    ENNReal.ofReal (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) :
  Integrable Gdrift P ∧
  (∀ᵐ ω ∂P, Gdrift ω ≤ 0) ∧
  (∫ ω, Gdrift ω ∂P) ≤ 0 := by
  have hμfinite : μT Set.univ < ∞ :=
    avram_wave8_22_original_BV_real_to_nnreal_finite_horizon_clock T μT hTime
  exact avram_wave8_22_original_BV_uniform_capped_generator_expected_nonpos
    X hBV q w x D T μT hTime A hAm K hK F hF hASet hKmeas
    B hBnonneg hμfinite hUniform Gdrift hGDef C hw_hjb hRegion
