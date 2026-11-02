-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_ruin_stopped_full_generator_residual_integrable_from_gaussian_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:46:20.762092+00:00
-- url     : https://prove2.me/submissions/ce5ede39-bb71-40a5-9811-3844e37795df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_discounted_gaussian_generator_split_export

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (E : Set (ℝ≥0 × Ω))
    (hE : MeasurableSet[𝓕.rightCont.predictable] E)
    (hG : IntegrableOn
      (fun p : ℝ≥0 × Ω => (if p.1 ≤ T then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
        else 0) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w
            (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1))) E μ)
    (hJ : IntegrableOn
      (fun p : ℝ≥0 × Ω => (if p.1 ≤ T then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
        else 0) *
        (X.c * deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
             (∫ z in Iio (0 : ℝ),
               SpectrallyNegativeLevy.generatorIntegrand w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) z ∂X.ν) -
             q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1))) E μ) :
    IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        (if p.1 ≤ T then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
        else 0) *
        (X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
          q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1))) E μ := by
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let K : ℝ≥0 × Ω → ℝ := fun p =>
    if p.1 ≤ T then
      Real.exp (-(q * (p.1 : ℝ))) *
        (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
    else 0
  have hSplit (p : ℝ≥0 × Ω) :
      K p * (X.generator w (Y p) - q * w (Y p)) =
        K p * (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)) +
          K p * (X.c * deriv w (Y p) +
            (∫ z in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν) -
               q * w (Y p)) := by
    by_cases ht : p.1 ≤ T
    · by_cases hτ : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
      · simpa [K, ht, hτ] using
          (avram_wave5_03a_original_discounted_gaussian_generator_split_export
            X w q (p.1 : ℝ) (Y p))
      · simp [K, ht, hτ]
    · simp [K, ht]
  have hGauss : IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        K p * (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p))) E μ := hG
  have hJump : IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        K p * (X.c * deriv w (Y p) +
          (∫ z in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν) -
             q * w (Y p))) E μ := hJ
  have hPair := hGauss.add hJump
  have hAE :
      (fun p : ℝ≥0 × Ω =>
        K p * (X.generator w (Y p) - q * w (Y p))) =ᵐ[μ.restrict E]
      (fun p : ℝ≥0 × Ω =>
        K p * (X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)) +
        K p * (X.c * deriv w (Y p) +
          (∫ z in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν) -
             q * w (Y p))) :=
    Filter.Eventually.of_forall hSplit
  change IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        K p * (X.generator w (Y p) - q * w (Y p))) E μ
  exact (integrable_congr hAE).2 hPair
