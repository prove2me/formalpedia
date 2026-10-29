-- Prove2me | solution 1 for AvramDividend.Classical.esscher_ordered_bounded_stops_history_future_increment_joint_reward_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:21:27.342786+00:00
-- url     : https://prove2.me/submissions/8be62b58-9d8e-41dd-9ebd-478f28ed09aa

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_history_future_increment_joint_product
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ σ : Ω → ℝ≥0)
    (hstopτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hstopσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ≥0)))
    (horder : ∀ ω, τ ω ≤ σ ω)
    (H : ℝ≥0) (hboundσ : ∀ ω, σ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYτ : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s}))
    (f : β → ℝ≥0∞) (hf : Measurable f)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    (∫⁻ ω, f (Y ω) *
      g (X.X (σ ω + u) ω - X.X (σ ω) ω) ∂QT) =
    (∫⁻ ω, f (Y ω) ∂Qτ) *
      (∫⁻ ω, g (X.X u ω) ∂QU) := by
  intro QT QU Qτ
  have hΦ := AvramDividend.Classical.esscher_ordered_bounded_stops_history_future_increment_joint_product
    X θ hθ τ σ hstopτ hstopσ horder H hboundσ u T hT Y hY hYτ
  have hfut := AvramDividend.Classical.levy_boundedStopping_stoppedFuturePath_measurable X σ hstopσ H hboundσ
  have hinc : Measurable (fun ω : Ω => X.X (σ ω + u) ω - X.X (σ ω) ω) :=
    (measurable_pi_apply u).comp hfut
  have hXu : Measurable (X.X u) := (X.adapted u).mono (𝓕.le u) le_rfl
  have hm : Measurable (fun ω : Ω => (Y ω, X.X (σ ω + u) ω - X.X (σ ω) ω)) := hY.prodMk hinc
  have h1 : (∫⁻ ω, f (Y ω) * g (X.X (σ ω + u) ω - X.X (σ ω) ω) ∂QT) =
      ∫⁻ p, f p.1 * g p.2 ∂(Measure.map (fun ω : Ω => (Y ω,
        X.X (σ ω + u) ω - X.X (σ ω) ω)) QT) := by
    rw [lintegral_map (by fun_prop) hm]
  rw [h1, hΦ, lintegral_prod_mul hf.aemeasurable hg.aemeasurable,
    lintegral_map hf hY, lintegral_map hg hXu]
