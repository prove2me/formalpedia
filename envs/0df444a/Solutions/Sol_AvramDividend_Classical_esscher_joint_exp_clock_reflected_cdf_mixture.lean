-- Prove2me | solution 1 for AvramDividend.Classical.esscher_joint_exp_clock_reflected_cdf_mixture
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:26:50.452367+00:00
-- url     : https://prove2.me/submissions/56fe3c2e-efbb-432c-b913-bf04fdbc357f

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_joint_clock_event_fibrewise_disintegration
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The authentic random-time tilted running-infimum CDF is the mixture
    of actual finite-horizon tilted running-infimum CDFs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p x : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
      {z : Ω × ℝ |
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x} =
    (∫⁻ t : ℝ,
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.ψ θ))))
        {ω : Ω | -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal t ∧ y = X.X s ω} ≤ x}
      ∂expMeasure p) := by
  letI : IsProbabilityMeasure P := X.isProbability
  letI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  have hD : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))) :=
    chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
      X θ (chat04_levy_joint_time_state_measurable X)
  have ht : Measurable (fun z : Ω × ℝ => Real.toNNReal z.2) :=
    measurable_real_toNNReal.comp measurable_snd
  have hRun : Measurable
      (fun z : Ω × ℝ =>
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) :=
    (levy_running_infimum_joint_time_path_measurable X).comp
      (ht.prodMk measurable_fst)
  have hA : MeasurableSet
      {z : Ω × ℝ |
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x} :=
    measurableSet_le hRun measurable_const
  exact esscher_joint_clock_event_fibrewise_disintegration
    P (expMeasure p)
    (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
    hD _ hA
