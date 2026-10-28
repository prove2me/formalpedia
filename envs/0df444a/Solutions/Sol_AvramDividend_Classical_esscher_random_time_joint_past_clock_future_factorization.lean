-- Prove2me | solution 1 for AvramDividend.Classical.esscher_random_time_joint_past_clock_future_factorization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:26:54.173815+00:00
-- url     : https://prove2.me/submissions/a049f2d2-0ef4-4bdf-97f9-2460223f705e

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- A random-time Esscher likelihood preserves past-event and clock-event
factorisation when every clock time in the event is after the past horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (s : ℝ≥0)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfuture : ∀ u ∈ B, s ≤ Real.toNNReal u) :
    ((P.prod (ProbabilityTheory.expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) (A ×ˢ B) =
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
        (ProbabilityTheory.expMeasure p) B := by
  haveI := X.isProbability
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  let D : Ω × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal
    (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
      (Real.toNNReal z.2 : ℝ) * X.ψ θ))
  let Qs : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))
  have hAm : MeasurableSet A := 𝓕.le s _ hA
  have hAB : MeasurableSet (A ×ˢ B) := hAm.prod hB
  have hfiber (u : ℝ) (hu : u ∈ B) :
      (∫⁻ ω in A, D (ω, u) ∂P) = Qs A := by
    calc
      (∫⁻ ω in A, D (ω, u) ∂P) =
          (P.withDensity (fun ω : Ω => ENNReal.ofReal
            (Real.exp (θ * X.X (Real.toNNReal u) ω -
              (Real.toNNReal u : ℝ) * X.ψ θ)))) A := by
              rw [withDensity_apply _ hAm]
      _ = Qs A := by
          exact (chat04_esscher_finite_horizon_laws_consistent_on_past_events
            X θ hθ s (Real.toNNReal u) (hfuture u hu) A hA).symm
  have hsections (u : ℝ) :
      (∫⁻ ω, (A ×ˢ B).indicator D (ω, u) ∂P) =
        B.indicator (fun _ => Qs A) u := by
    by_cases hu : u ∈ B
    · have hpoint : (fun ω => (A ×ˢ B).indicator D (ω, u)) =
          A.indicator (fun ω => D (ω, u)) := by
        funext ω
        by_cases hω : ω ∈ A
        · simp [Set.indicator, hω, hu]
        · simp [Set.indicator, hω, hu]
      rw [hpoint, lintegral_indicator hAm, hfiber u hu]
      simp [Set.indicator, hu]
    · have hpoint : (fun ω => (A ×ˢ B).indicator D (ω, u)) =
          fun _ => 0 := by
        funext ω
        simp [Set.indicator, hu]
      rw [hpoint]
      simp [Set.indicator, hu]
  calc
    ((P.prod (ProbabilityTheory.expMeasure p)).withDensity D) (A ×ˢ B) =
        (∫⁻ z, (A ×ˢ B).indicator D z
          ∂(P.prod (ProbabilityTheory.expMeasure p))) := by
            rw [withDensity_apply _ hAB]
            exact (lintegral_indicator hAB D).symm
    _ = ∫⁻ u : ℝ, ∫⁻ ω, (A ×ˢ B).indicator D (ω, u) ∂P
          ∂(ProbabilityTheory.expMeasure p) :=
      lintegral_prod_symm _ ((hJoint.indicator hAB).aemeasurable)
    _ = ∫⁻ u, B.indicator (fun _ => Qs A) u
          ∂(ProbabilityTheory.expMeasure p) := by
      congr 1
      funext u
      exact hsections u
    _ = Qs A * (ProbabilityTheory.expMeasure p) B := by
      rw [lintegral_indicator hB]
      simp [mul_comm]
