-- Prove2me | solution 1 for AvramDividend.Classical.esscher_true_random_clock_reflected_law_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T19:15:57.690346+00:00
-- url     : https://prove2.me/submissions/e04e8e92-cb28-44ba-beac-7e25b1715713

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Genuine exponential-horizon Esscher reflected-infimum pushforward is a probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) :
    IsProbabilityMeasure
      (((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))).map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1})) := by
  have hD : Measurable (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))) :=
    chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
      X θ (chat04_levy_joint_time_state_measurable X)
  have ht : Measurable (fun z : Ω × ℝ => Real.toNNReal z.2) :=
    measurable_real_toNNReal.comp measurable_snd
  have hR : Measurable (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) :=
    (levy_running_infimum_joint_time_path_measurable X).comp
      (ht.prodMk measurable_fst)
  letI : IsProbabilityMeasure
    ((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :=
    chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
      X θ p hθ hp hD
  exact Measure.isProbabilityMeasure_map hR.aemeasurable
