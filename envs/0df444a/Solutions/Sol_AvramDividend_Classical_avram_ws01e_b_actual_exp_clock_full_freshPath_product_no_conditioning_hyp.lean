-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_exp_clock_full_freshPath_product_no_conditioning_hyp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:12:47.288833+00:00
-- url     : https://prove2.me/submissions/86429f59-4083-431b-851c-e893fe6a577c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_independent_clock_positive_survival_event
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_toNNReal_strict_tail
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_exp_clock_residual_full_law
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (hStop : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (p : ℝ) (hp : 0 < p) :
    Measure.map
      (fun z : Ω × ℝ =>
        ((z.2.toNNReal : ℝ) - (τ z.1 : ℝ),
          fun s : ℝ≥0 =>
            X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1))
      ((P.prod (expMeasure p))[|
        {z : Ω × ℝ | τ z.1 < z.2.toNNReal}]) =
    (Measure.map (fun t : ℝ => (t.toNNReal : ℝ))
        (expMeasure p)).prod
      (Measure.map (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) P) := by
  have := isProbabilityMeasure_expMeasure hp
  have hPos : (P.prod (expMeasure p)) {z : Ω × ℝ | τ z.1 < z.2.toNNReal} ≠ 0 :=
    avram_ws01e_b_independent_clock_positive_survival_event P (expMeasure p) τ hτ
      (fun t : ℝ => t.toNNReal) measurable_real_toNNReal (fun a => by
        rw [avram_ws01e_b_exp_clock_toNNReal_strict_tail p hp a]
        exact ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  rw [avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law X τ hτ hStop
      (expMeasure p) (fun t : ℝ => t.toNNReal) measurable_real_toNNReal hPos,
    avram_ws01e_b_actual_exp_clock_residual_full_law P τ hτ (fun _ => ()) measurable_const
      (indepFun_const_right _ _) p hp hPos]
