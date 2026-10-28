-- Prove2me | solution 1 for AvramDividend.Classical.esscher_clock_supported_stopped_event_laws_agree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:51:26.039863+00:00
-- url     : https://prove2.me/submissions/5fb159e9-2873-4a8c-98eb-cdc45e07d803

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- On clock-supported adapted events the random-time Esscher density
and the terminal independent-clock product law give the same measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0)
    {ν : Measure ℝ} [SFinite ν]
    (E : Set (Ω × ℝ))
    (hE : MeasurableSet E)
    (hSlice : ∀ t : ℝ,
      @MeasurableSet Ω (𝓕 (min t.toNNReal T))
        {ω : Ω | (ω, t) ∈ E})
    (hSupport : ∀ (ω : Ω) (t : ℝ), (ω, t) ∈ E → t.toNNReal ≤ T)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))) :
    ((P.prod ν).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))) E =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν) E := by
  haveI := X.isProbability
  haveI : IsProbabilityMeasure
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) :=
    chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  let D : Ω × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal
    (Real.exp (θ * X.X z.2.toNNReal z.1 -
      (z.2.toNNReal : ℝ) * X.ψ θ))
  let Q : ℝ≥0 → Measure Ω := fun t => P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)))
  let A : ℝ → Set Ω := fun t => {ω | (ω, t) ∈ E}
  have hA (t : ℝ) : MeasurableSet (A t) :=
    𝓕.le (min t.toNNReal T) _ (hSlice t)
  have hFiber (t : ℝ) :
      (∫⁻ ω, E.indicator D (ω, t) ∂P) =
      (∫⁻ ω, E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, t) ∂(Q T)) := by
    have hLf : (fun ω : Ω => E.indicator D (ω, t)) =
        (A t).indicator (fun ω => D (ω, t)) := by
      funext ω
      rfl
    have hRf : (fun ω : Ω => E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, t)) =
        (A t).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      rfl
    by_cases ht : t.toNNReal ≤ T
    · have hAearly : @MeasurableSet Ω (𝓕 t.toNNReal) (A t) := by
        have hs : @MeasurableSet Ω (𝓕 (min t.toNNReal T)) (A t) := hSlice t
        rw [min_eq_left ht] at hs
        exact hs
      calc
        (∫⁻ ω, E.indicator D (ω, t) ∂P) =
            (∫⁻ ω in A t, D (ω, t) ∂P) := by
              rw [hLf, lintegral_indicator (hA t)]
        _ = Q t.toNNReal (A t) := by
              rw [withDensity_apply _ (hA t)]
        _ = Q T (A t) := by
              exact (chat04_esscher_finite_horizon_laws_consistent_on_past_events
                X θ hθ t.toNNReal T ht (A t) hAearly)
        _ = (∫⁻ ω in A t, (1 : ℝ≥0∞) ∂(Q T)) := by simp
        _ = (∫⁻ ω, E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, t) ∂(Q T)) := by
              rw [hRf, lintegral_indicator (hA t)]
    · have hno (ω : Ω) : (ω, t) ∉ E := by
        intro he
        exact ht (hSupport ω t he)
      have hl : (fun ω : Ω => E.indicator D (ω, t)) = fun _ => 0 := by
        funext ω
        simp [Set.indicator, hno ω]
      have hr : (fun ω : Ω => E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, t)) =
          fun _ => 0 := by
        funext ω
        simp [Set.indicator, hno ω]
      rw [hl, hr]
      simp
  calc
    ((P.prod ν).withDensity D) E =
        (∫⁻ z, E.indicator D z ∂(P.prod ν)) := by
          rw [withDensity_apply _ hE]
          exact (lintegral_indicator hE D).symm
    _ = (∫⁻ t : ℝ, ∫⁻ ω, E.indicator D (ω, t) ∂P ∂ν) :=
          lintegral_prod_symm _ ((hJoint.indicator hE).aemeasurable)
    _ = (∫⁻ t : ℝ, ∫⁻ ω,
          E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, t) ∂(Q T) ∂ν) := by
            congr 1
            funext t
            exact hFiber t
    _ = (∫⁻ z, E.indicator (fun _ => (1 : ℝ≥0∞)) z ∂((Q T).prod ν)) :=
          (lintegral_prod_symm _
            ((measurable_const.indicator hE).aemeasurable)).symm
    _ = ((Q T).prod ν) E := by
          rw [lintegral_indicator hE]
          simp
