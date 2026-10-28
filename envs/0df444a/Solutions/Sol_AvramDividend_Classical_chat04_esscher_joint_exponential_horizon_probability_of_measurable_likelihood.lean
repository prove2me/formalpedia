-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:49:59.989701+00:00
-- url     : https://prove2.me/submissions/fee8fed9-f317-420c-ad89-cee28cf9b185

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_fibrewise_normalized_joint_tilt_probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
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
            ((Real.toNNReal z.2 : ℝ)) * X.ψ θ)))) :
    IsProbabilityMeasure
      ((P.prod (ProbabilityTheory.expMeasure p)).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            ((Real.toNNReal z.2 : ℝ)) * X.ψ θ)))) := by
  haveI := X.isProbability
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  refine chat04_fibrewise_normalized_joint_tilt_probability P _ _ hJoint fun t => ?_
  have h := chat04_esscher_weighted_finite_horizon_probability X (Real.toNNReal t) θ hθ
  have h1 := h.measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  simpa [SpectrallyNegativeLevy.ψ] using h1
