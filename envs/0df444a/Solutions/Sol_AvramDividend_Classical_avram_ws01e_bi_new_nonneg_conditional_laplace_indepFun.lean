-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_nonneg_conditional_laplace_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:58:01.64292+00:00
-- url     : https://prove2.me/submissions/60dfef7b-5193-4fdb-944a-170fd566007f

import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_conditional_mgf_indepFun

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped ProbabilityTheory ENNReal

/-- All positive conditional Laplace moments of a nonnegative drawdown
identify its entire conditional law and imply independence. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R D : Ω → ℝ) (hR : Measurable R) (hD : Measurable D)
    (hDnonneg : ∀ ω : Ω, 0 ≤ D ω)
    (hLap : ∀ a : ℝ, P (R ⁻¹' Set.Ioi a) ≠ 0 →
      ∀ β : ℝ, 0 < β →
        (∫ ω : Ω, Real.exp (-(β * D ω)) ∂(P[|R ⁻¹' Set.Ioi a])) =
          ∫ ω : Ω, Real.exp (-(β * D ω)) ∂P) :
    IndepFun R D P := by
  have hneg : Measurable (fun ω : Ω => -D ω) := hD.neg
  have hbound (β : ℝ) (hβ : 0 < β) (ω : Ω) :
      ‖Real.exp (-(β * D ω))‖ ≤ (1 : ℝ) := by
    have hmul : 0 ≤ β * D ω := mul_nonneg hβ.le (hDnonneg ω)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hmul)
  have hind : IndepFun R (fun ω : Ω => -D ω) P := by
    apply AvramDividend.Classical.avram_ws01e_bi_new_conditional_mgf_indepFun
      P R (fun ω : Ω => -D ω) hR hneg
    · intro a ha β hβ
      haveI : IsProbabilityMeasure (P[|R ⁻¹' Set.Ioi a]) :=
        ProbabilityTheory.cond_isProbabilityMeasure ha
      have hf : Measurable (fun ω : Ω => Real.exp (-(β * D ω))) := by fun_prop
      have hfCond : AEStronglyMeasurable
          (fun ω : Ω => Real.exp (-(β * D ω))) (P[|R ⁻¹' Set.Ioi a]) :=
        hf.aestronglyMeasurable
      have hfP : AEStronglyMeasurable
          (fun ω : Ω => Real.exp (-(β * D ω))) P :=
        hf.aestronglyMeasurable
      have hcond : Integrable (fun ω : Ω => Real.exp (-(β * D ω)))
          (P[|R ⁻¹' Set.Ioi a]) :=
        Integrable.of_bound hfCond 1 (ae_of_all _ (hbound β hβ))
      have hall : Integrable (fun ω : Ω => Real.exp (-(β * D ω))) P :=
        Integrable.of_bound hfP 1 (ae_of_all _ (hbound β hβ))
      have hm : Measurable (fun y : ℝ => Real.exp (β * y)) := by fun_prop
      constructor
      · rw [integrable_map_measure hm.aestronglyMeasurable hneg.aemeasurable]
        simpa only [Function.comp_def, mul_neg] using hcond
      · rw [integrable_map_measure hm.aestronglyMeasurable hneg.aemeasurable]
        simpa only [Function.comp_def, mul_neg] using hall
    · intro a ha β hβ
      have hm : Measurable (fun y : ℝ => Real.exp (β * y)) := by fun_prop
      rw [integral_map hneg.aemeasurable hm.aestronglyMeasurable,
        integral_map hneg.aemeasurable hm.aestronglyMeasurable]
      simpa only [mul_neg] using hLap a ha β hβ
  have hident : (-(fun ω : Ω => -D ω)) = D := by
    funext ω
    simp only [Pi.neg_apply, neg_neg]
  simpa only [hident] using hind.neg_right
