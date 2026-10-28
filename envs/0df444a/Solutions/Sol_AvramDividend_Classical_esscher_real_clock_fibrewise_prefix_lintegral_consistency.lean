-- Prove2me | solution 1 for AvramDividend.Classical.esscher_real_clock_fibrewise_prefix_lintegral_consistency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:26:58.267991+00:00
-- url     : https://prove2.me/submissions/7116ee7c-dce2-4ab5-b787-c63d158fb789

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_finite_prefix_lintegral_consistency
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- A true real-valued independent exponential-clock coordinate is compatible
with the clock-dependent capped Esscher path density on adapted sections. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0)
    {ν : Measure ℝ} [SFinite ν]
    (F : Ω × ℝ → ℝ≥0∞)
    (hF : Measurable F)
    (hSlice : ∀ t : ℝ,
      Measurable[𝓕 (min t.toNNReal T)] (fun ω : Ω => F (ω, t))) :
    (∫⁻ z, F z ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν) =
    (∫⁻ t : ℝ, (∫⁻ ω, F (ω, t) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (min t.toNNReal T) ω -
          ((min t.toNNReal T : ℝ≥0) : ℝ) * X.ψ θ))))) ∂ν) := by
  haveI : IsProbabilityMeasure
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) :=
    chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  calc
    (∫⁻ z, F z ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν) =
      (∫⁻ t : ℝ, (∫⁻ ω, F (ω, t) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) ∂ν) :=
            lintegral_prod_symm' F hF
    _ = (∫⁻ t : ℝ, (∫⁻ ω, F (ω, t) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (min t.toNNReal T) ω -
          ((min t.toNNReal T : ℝ≥0) : ℝ) * X.ψ θ))))) ∂ν) := by
            have heq :
                (fun t : ℝ => ∫⁻ ω, F (ω, t) ∂
                  (P.withDensity (fun ω : Ω => ENNReal.ofReal
                    (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
                (fun t : ℝ => ∫⁻ ω, F (ω, t) ∂
                  (P.withDensity (fun ω : Ω => ENNReal.ofReal
                    (Real.exp (θ * X.X (min t.toNNReal T) ω -
                      ((min t.toNNReal T : ℝ≥0) : ℝ) * X.ψ θ))))) := by
                      funext t
                      exact esscher_finite_prefix_lintegral_consistency
                        X θ hθ (min t.toNNReal T) T
                          (min_le_right t.toNNReal T)
                          (fun ω => F (ω, t)) (hSlice t)
            rw [heq]
