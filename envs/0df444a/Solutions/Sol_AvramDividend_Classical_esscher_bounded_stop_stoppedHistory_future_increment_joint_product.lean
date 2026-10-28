-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_future_increment_joint_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T19:17:03.175902+00:00
-- url     : https://prove2.me/submissions/1d9e6a76-29d6-47ab-8964-cc632ce38923

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_stopped_likelihood_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYstopped : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let QStop : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => (Y ω,
        X.X (τ ω + u) ω - X.X (τ ω) ω)) QT =
      (Measure.map Y QStop).prod (Measure.map (X.X u) QU) := by
  intro QT QU QStop
  let Δ : Ω → ℝ := fun ω =>
    X.X (τ ω + u) ω - X.X (τ ω) ω
  have hΔ : Measurable Δ :=
    (measurable_pi_apply u).comp
      (levy_boundedStopping_stoppedFuturePath_measurable
        X τ hstop H hbound)
  have hJoint : Measurable (fun ω : Ω => (Y ω, Δ ω)) :=
    hY.prodMk hΔ
  haveI : IsProbabilityMeasure QT :=
    chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  haveI : IsProbabilityMeasure QU :=
    chat04_esscher_weighted_finite_horizon_probability X u θ hθ
  have hXu : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  haveI : IsFiniteMeasure
      (Measure.map (fun ω : Ω => (Y ω, Δ ω)) QT) :=
    Measure.isFiniteMeasure_map QT (fun ω : Ω => (Y ω, Δ ω))
  haveI : IsFiniteMeasure (Measure.map (X.X u) QU) :=
    Measure.isFiniteMeasure_map QU (X.X u)
  change Measure.map (fun ω : Ω => (Y ω, Δ ω)) QT =
    (Measure.map Y QStop).prod (Measure.map (X.X u) QU)
  apply Measure.ext_prod
  intro C D hC hD
  rw [Measure.map_apply hJoint (hC.prod hD), Measure.prod_prod]
  rw [Measure.map_apply hY hC, Measure.map_apply hXu hD]
  change QT ((Y ⁻¹' C) ∩ {ω : Ω | X.X (τ ω + u) ω -
    X.X (τ ω) ω ∈ D}) =
      QStop (Y ⁻¹' C) * QU ((X.X u) ⁻¹' D)
  exact esscher_bounded_stop_future_increment_stopped_likelihood_factor
    X θ hθ τ hstop H hbound u T hT
    (Y ⁻¹' C) (hYstopped C hC) D hD
