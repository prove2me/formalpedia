-- Prove2me | solution 1 for AvramDividend.Classical.esscher_clock_fibrewise_prefix_lintegral_consistency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:56:35.192783+00:00
-- url     : https://prove2.me/submissions/9ace68d3-7b25-459d-a1e3-d8a485950c6f

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_finite_prefix_lintegral_consistency
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- A terminal Esscher path law with independent clock matches the
clock-by-clock Esscher density at the capped realised clock, for every
jointly measurable observable of that clock's available path prefix. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0)
    {ν : Measure ℝ≥0} [SFinite ν]
    (F : Ω × ℝ≥0 → ℝ≥0∞)
    (hF : Measurable F)
    (hSlice : ∀ t : ℝ≥0,
      Measurable[𝓕 (min t T)] (fun ω : Ω => F (ω, t))) :
    (∫⁻ z, F z ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν) =
    (∫⁻ t : ℝ≥0, (∫⁻ ω, F (ω, t) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (min t T) ω -
          ((min t T : ℝ≥0) : ℝ) * X.ψ θ))))) ∂ν) := by
  haveI : IsProbabilityMeasure
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) :=
    chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  calc
    (∫⁻ z, F z ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν) =
      (∫⁻ t : ℝ≥0, (∫⁻ ω, F (ω, t) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) ∂ν) :=
            lintegral_prod_symm' F hF
    _ = (∫⁻ t : ℝ≥0, (∫⁻ ω, F (ω, t) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (min t T) ω -
          ((min t T : ℝ≥0) : ℝ) * X.ψ θ))))) ∂ν) := by
            have heq :
                (fun t : ℝ≥0 => ∫⁻ ω, F (ω, t) ∂
                  (P.withDensity (fun ω : Ω => ENNReal.ofReal
                    (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
                (fun t : ℝ≥0 => ∫⁻ ω, F (ω, t) ∂
                  (P.withDensity (fun ω : Ω => ENNReal.ofReal
                    (Real.exp (θ * X.X (min t T) ω -
                      ((min t T : ℝ≥0) : ℝ) * X.ψ θ))))) := by
                      funext t
                      exact esscher_finite_prefix_lintegral_consistency
                        X θ hθ (min t T) T (min_le_right t T)
                          (fun ω => F (ω, t)) (hSlice t)
            rw [heq]
