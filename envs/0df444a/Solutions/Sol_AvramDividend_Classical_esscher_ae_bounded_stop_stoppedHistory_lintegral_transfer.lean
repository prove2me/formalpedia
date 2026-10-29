-- Prove2me | solution 1 for AvramDividend.Classical.esscher_ae_bounded_stop_stoppedHistory_lintegral_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:51:23.015858+00:00
-- url     : https://prove2.me/submissions/d76db4cf-cc42-4717-9cad-eeba00335a44

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_ae_bounded_stop_stoppedHistory_observable_map_law
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (haeBound : ∀ᵐ ω ∂P, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYstopped : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s}))
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, g (Y ω) ∂
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
    (∫⁻ ω, g (Y ω) ∂
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ θ))))) := by
  let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
  let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ)))
  have hmap : Measure.map Y QT = Measure.map Y Qτ :=
    esscher_ae_bounded_stop_stoppedHistory_observable_map_law
      X θ hθ τ hstop H haeBound T hT Y hY hYstopped
  change (∫⁻ ω, g (Y ω) ∂QT) = ∫⁻ ω, g (Y ω) ∂Qτ
  calc
    (∫⁻ ω, g (Y ω) ∂QT) =
        ∫⁻ y, g y ∂Measure.map Y QT :=
      (lintegral_map hg hY).symm
    _ = ∫⁻ y, g y ∂Measure.map Y Qτ := by rw [hmap]
    _ = ∫⁻ ω, g (Y ω) ∂Qτ := lintegral_map hg hY
