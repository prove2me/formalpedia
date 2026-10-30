-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_true_Qp_strict_lower_killing_eq_closed_survival_reward
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T11:16:16.166254+00:00
-- url     : https://prove2.me/submissions/d2381868-cc67-4e35-acb5-7f1408e460e3

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_true_strict_closed_exponential_product_integral_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_strict_lower_killing_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_closed_history_lower_survival_joint_measurable_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) (θ : ℝ) (x : ℝ)
    (R : Ω × ℝ → ℝ≥0∞) (hR : Measurable R) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (ProbabilityTheory.expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧
         ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}).indicator R z
       ∂Qp) =
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧
         ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
           -x ≤ X.X s z.1}).indicator R z
       ∂Qp)) := by
  intro Qp
  set f : Ω × ℝ → ℝ≥0∞ := fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)) with hf
  have hjoint := AvramDividend.Classical.chat04_levy_joint_time_state_measurable X
  have hXm : Measurable (fun z : Ω × ℝ => X.X (Real.toNNReal z.2) z.1) :=
    hjoint.comp ((measurable_snd.real_toNNReal).prodMk measurable_fst)
  have hfm : Measurable f := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact (measurable_const.mul hXm).sub
      ((measurable_snd.real_toNNReal.coe_nnreal_real).mul_const _)
  have hA := AvramDividend.Classical.chat04_exponential_clock_strict_lower_killing_joint_measurable X (-x)
  have hB := AvramDividend.Classical.chat04_closed_history_lower_survival_joint_measurable_ws01a X x
  have key := AvramDividend.Classical.chat04_true_strict_closed_exponential_product_integral_ws01a
    P X p hp x (fun z => f z * R z) (hfm.mul hR)
  have conv : ∀ S : Set (Ω × ℝ), MeasurableSet S →
      ∫⁻ z, S.indicator R z ∂Qp = ∫⁻ z, S.indicator (fun z => f z * R z) z
        ∂(P.prod (ProbabilityTheory.expMeasure p)) := by
    intro S hS
    rw [lintegral_withDensity_eq_lintegral_mul _ hfm (hR.indicator hS)]
    refine lintegral_congr (fun z => ?_)
    by_cases hz : z ∈ S <;> simp [Set.indicator, hz]
  rw [conv _ hA, conv _ hB]
  exact key
