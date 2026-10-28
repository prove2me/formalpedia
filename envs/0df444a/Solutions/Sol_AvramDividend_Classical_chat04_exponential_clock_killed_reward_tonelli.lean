-- Prove2me | solution 1 for AvramDividend.Classical.chat04_exponential_clock_killed_reward_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T12:47:28.555993+00:00
-- url     : https://prove2.me/submissions/71bcfed4-d1af-41b9-a68c-bfe41b832a0b

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Independent exponential observation evaluates a killed reward through its
    genuine stochastic time-resolvent density. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp : 0 < p)
    (survival : Set (Ω × ℝ)) (hSurv : MeasurableSet survival)
    (reward : Ω × ℝ → ENNReal) (hReward : Measurable reward) :
    (∫⁻ z : Ω × ℝ, survival.indicator reward z
        ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF p t *
       (∫⁻ ω : Ω, survival.indicator reward (ω, t) ∂P) ∂volume) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  have hpay : Measurable (survival.indicator reward) :=
    hReward.indicator hSurv
  have hinner : Measurable
      (fun t : ℝ => ∫⁻ ω : Ω,
        survival.indicator reward (ω, t) ∂P) :=
    hpay.lintegral_prod_left'
  have hpdf : Measurable (ProbabilityTheory.exponentialPDF p) :=
    (ProbabilityTheory.measurable_exponentialPDFReal p).ennreal_ofReal
  rw [lintegral_prod_symm (survival.indicator reward) hpay.aemeasurable]
  change (∫⁻ t : ℝ,
       (∫⁻ ω : Ω, survival.indicator reward (ω, t) ∂P)
       ∂(volume.withDensity (ProbabilityTheory.exponentialPDF p))) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume hpdf hinner]
  rfl
