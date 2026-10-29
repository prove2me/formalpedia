-- Prove2me | solution 1 for AvramDividend.Classical.esscher_ordered_bounded_stops_history_future_increment_joint_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:19:27.846489+00:00
-- url     : https://prove2.me/submissions/e2e4de11-d01f-44bd-8bdd-9b55a63be2f1

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_history_future_increment_joint_product
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable
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
    (R : β × ℝ → ℝ≥0∞) (hR : Measurable R) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    (∫⁻ ω, R (Y ω,
      X.X (σ ω + u) ω - X.X (σ ω) ω) ∂QT) =
    ∫⁻ y : β, (∫⁻ z : ℝ, R (y, z) ∂Measure.map (X.X u) QU) ∂
      Measure.map Y Qτ := by
  intro QT QU Qτ
  let D : Ω → ℝ :=
    fun ω => X.X (σ ω + u) ω - X.X (σ ω) ω
  let m1 : Measure β := Measure.map Y Qτ
  let m2 : Measure ℝ := Measure.map (X.X u) QU
  have hXu : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  have hD : Measurable D :=
    (measurable_pi_apply u).comp
      (levy_boundedStopping_stoppedFuturePath_measurable
        X σ hstopσ H hboundσ)
  have hPair : Measurable (fun ω : Ω => (Y ω, D ω)) :=
    hY.prodMk hD
  haveI : IsProbabilityMeasure QU :=
    chat04_esscher_weighted_finite_horizon_probability X u θ hθ
  haveI : IsProbabilityMeasure m2 := by
    dsimp [m2]
    exact Measure.isProbabilityMeasure_map hXu.aemeasurable
  have hLaw : Measure.map (fun ω : Ω => (Y ω, D ω)) QT =
      m1.prod m2 := by
    simpa only [D, m1, m2] using
      (esscher_ordered_bounded_stops_history_future_increment_joint_product
        X θ hθ τ σ hstopτ hstopσ horder H hboundσ
          u T hT Y hY hYτ)
  calc
    (∫⁻ ω, R (Y ω, D ω) ∂QT) =
        ∫⁻ w : β × ℝ, R w ∂
          Measure.map (fun ω : Ω => (Y ω, D ω)) QT :=
      (lintegral_map hR hPair).symm
    _ = ∫⁻ w : β × ℝ, R w ∂m1.prod m2 := by
      rw [hLaw]
    _ = ∫⁻ y : β, (∫⁻ z : ℝ, R (y, z) ∂m2) ∂m1 :=
      lintegral_prod R hR.aemeasurable
