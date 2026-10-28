-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_joint_exponential_clock_marginal_of_measurable_likelihood
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T10:39:52.613603+00:00
-- url     : https://prove2.me/submissions/0e9229f6-e1e1-4865-98eb-e601956c6c7f

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_chat04_fibrewise_normalized_joint_tilt_clock_marginal
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
    (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
      (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    Measure.map Prod.snd
      ((P.prod (ProbabilityTheory.expMeasure p)).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
    (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
      (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) =
      ProbabilityTheory.expMeasure p := by
  haveI := X.isProbability
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  refine chat04_fibrewise_normalized_joint_tilt_clock_marginal
    P _ _ hJoint fun t => ?_
  have h := chat04_esscher_weighted_finite_horizon_probability
    X (Real.toNNReal t) θ hθ
  have h1 := h.measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  simpa [SpectrallyNegativeLevy.ψ] using h1
