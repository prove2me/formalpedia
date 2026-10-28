-- Prove2me | solution 1 for AvramDividend.Classical.esscher_fixed_terminal_independent_exponential_clock_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:00:47.895709+00:00
-- url     : https://prove2.me/submissions/e570e91f-57b2-412b-9e0b-572f2ac56cc9

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- A fixed-terminal Esscher change of path law leaves an independent exponential
clock independent of all events observed before the terminal time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (p : ℝ) (hp : 0 < p)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (B : Set ℝ) :
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)))).prod
      (ProbabilityTheory.expMeasure p)) (A ×ˢ B) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
      (ProbabilityTheory.expMeasure p) B := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  rw [Measure.prod_prod]
  exact congrArg
    (fun r : ℝ≥0∞ => r * (ProbabilityTheory.expMeasure p) B)
    (chat04_esscher_finite_horizon_laws_consistent_on_past_events
      X θ hθ s t hst A hA).symm
