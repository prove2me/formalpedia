-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_killed_scale_exponential_clock_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:14:37.872535+00:00
-- url     : https://prove2.me/submissions/2a46c9af-8729-44c9-b991-e0f2f27a723c

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_killed_reward_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_strict_lower_killing_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_continuous_of_zero_origin
import Mathlib.Probability.Distributions.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The true lower-killed q-scale exponential-clock reward is its discounted time integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q p : ℝ) (hq : 0 < q) (hp : 0 < p)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (x : ℝ) :
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
  have hZero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hContinuous : Continuous W :=
    scaleFunction_global_continuous_of_zero_origin X q W hW hZero
  have hReward : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (-q * z.2) *
        W (x + X.X (Real.toNNReal z.2) z.1))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · exact Real.continuous_exp.measurable.comp
        (measurable_const.mul measurable_snd)
    · exact hContinuous.measurable.comp (measurable_const.add hState)
  exact chat04_exponential_clock_killed_reward_tonelli P p hp
    _ (chat04_exponential_clock_strict_lower_killing_joint_measurable X (-x))
    _ hReward
