-- Prove2me | solution 1 for AvramDividend.Classical.chat04_true_killed_scale_strict_closed_exp_clock_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T09:34:59.705978+00:00
-- url     : https://prove2.me/submissions/9dad914d-3da4-463d-8097-dfb8d83dca27

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_true_strict_closed_exponential_product_integral_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

/-- The genuine strict lower first-passage and complete closed-history killed
    discounted q-scale rewards agree at an independent exponential clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p q : ℝ) (hp : 0 < p) (x : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧
        ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}).indicator
        (fun z => ENNReal.ofReal
          (Real.exp (-(q * z.2)) *
            W (x + X.X (Real.toNNReal z.2) z.1))) z
      ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧
        ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}).indicator
        (fun z => ENNReal.ofReal
          (Real.exp (-(q * z.2)) *
            W (x + X.X (Real.toNNReal z.2) z.1))) z
      ∂(P.prod (ProbabilityTheory.expMeasure p))) := by
  let R : Ω × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal
    (Real.exp (-(q * z.2)) * W (x + X.X (Real.toNNReal z.2) z.1))
  have hTime : Measurable (fun z : Ω × ℝ =>
      (Real.toNNReal z.2, z.1)) :=
    (measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst
  have hXt : Measurable (fun z : Ω × ℝ =>
      X.X (Real.toNNReal z.2) z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp hTime
  have hWm : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hR : Measurable R := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · exact Real.continuous_exp.measurable.comp
        ((measurable_const.mul measurable_snd).neg)
    · exact hWm.comp (measurable_const.add hXt)
  simpa only [R] using
    (chat04_true_strict_closed_exponential_product_integral_ws01a
      P X p hp x R hR)
