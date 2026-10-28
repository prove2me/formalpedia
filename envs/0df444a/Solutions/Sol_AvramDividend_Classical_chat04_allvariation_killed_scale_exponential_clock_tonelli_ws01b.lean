-- Prove2me | solution 1 for AvramDividend.Classical.chat04_allvariation_killed_scale_exponential_clock_tonelli_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:42:54.461403+00:00
-- url     : https://prove2.me/submissions/6f302bcc-1491-454c-8a2d-4718775fc9fe

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_killed_reward_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_strict_lower_killing_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Mathlib.Probability.Distributions.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Exact exponential-clock time-resolvent formula for every q-scale function, including BV. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q p : ℝ) (hq : 0 < q) (hp : 0 < p)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) :
    (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧
        ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}).indicator
        (fun z => ENNReal.ofReal
          (Real.exp (-q * z.2) * W (x + X.X (Real.toNNReal z.2) z.1))) z
      ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF p t *
      (∫⁻ ω : Ω,
        ({z : Ω × ℝ | 0 ≤ z.2 ∧
          ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}).indicator
          (fun z => ENNReal.ofReal
            (Real.exp (-q * z.2) * W (x + X.X (Real.toNNReal z.2) z.1)))
          (ω, t) ∂P) ∂volume) := by
  have hJoint := chat04_levy_joint_time_state_measurable X
  have hTime : Measurable (fun z : Ω × ℝ =>
      (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hState : Measurable (fun z : Ω × ℝ =>
      X.X (Real.toNNReal z.2) z.1) := hJoint.comp hTime
  have hWMeas : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hReward : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (-q * z.2) *
        W (x + X.X (Real.toNNReal z.2) z.1))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · exact Real.continuous_exp.measurable.comp
        (measurable_const.mul measurable_snd)
    · exact hWMeas.comp (measurable_const.add hState)
  exact chat04_exponential_clock_killed_reward_tonelli P p hp
    _ (chat04_exponential_clock_strict_lower_killing_joint_measurable X (-x))
    _ hReward