-- Prove2me | solution 1 for AvramDividend.Classical.esscher_joint_clock_finite_prefix_lintegral_consistency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:31:13.158998+00:00
-- url     : https://prove2.me/submissions/9eb51fc5-bc25-4df0-8354-3b69df5ca085

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_finite_prefix_lintegral_consistency
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Joint observations of an independent clock and an earlier path prefix have a
terminal-horizon-independent integral, with no infinite-path extension needed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s T : ℝ≥0) (hsT : s ≤ T)
    {ν : Measure ℝ} [SFinite ν]
    (F : Ω × ℝ → ℝ≥0∞)
    (hF : Measurable F)
    (hSlice : ∀ t : ℝ, Measurable[𝓕 s] (fun ω : Ω => F (ω, t))) :
    (∫⁻ z, F z ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν) =
    (∫⁻ z, F z ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))).prod ν) := by
  haveI : IsProbabilityMeasure
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) :=
    chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  haveI : IsProbabilityMeasure
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) :=
    chat04_esscher_weighted_finite_horizon_probability X s θ hθ
  calc
    (∫⁻ z, F z ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν) =
      ∫⁻ t : ℝ, (∫⁻ ω, F (ω, t) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) ∂ν :=
            lintegral_prod_symm' F hF
    _ = ∫⁻ t : ℝ, (∫⁻ ω, F (ω, t) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))) ∂ν := by
            have heq :
                (fun t : ℝ => ∫⁻ ω, F (ω, t) ∂
                  (P.withDensity (fun ω : Ω => ENNReal.ofReal
                    (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
                (fun t : ℝ => ∫⁻ ω, F (ω, t) ∂
                  (P.withDensity (fun ω : Ω => ENNReal.ofReal
                    (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))) := by
                      funext t
                      exact esscher_finite_prefix_lintegral_consistency
                        X θ hθ s T hsT (fun ω => F (ω, t)) (hSlice t)
            rw [heq]
    _ = (∫⁻ z, F z ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))).prod ν) :=
          (lintegral_prod_symm' F hF).symm
