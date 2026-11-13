-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB138_bounded_joint_measurable_pair_nested_squared_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:57:31.775074+00:00
-- url     : https://prove2.me/submissions/d77ea049-d60c-4071-8486-b122e6e81275

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gbB129_bounded_measurable_squared_difference_integrable
import Theorems.Thm_AvramDividend_Classical_avram_gbB132_bounded_joint_measurable_squared_error_outer_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
noncomputable section

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f g : α × β → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ z, |f z| ≤ B) (hgb : ∀ z, |g z| ≤ B) :
    (∀ a, Integrable (fun b => (f (a, b) - g (a, b)) ^ 2) ν) ∧
    Integrable (fun a => ∫ b, (f (a, b) - g (a, b)) ^ 2 ∂ν) μ := by
  constructor
  · intro a
    have hpair : Measurable (fun b : β => (a, b)) :=
      measurable_const.prodMk measurable_id
    exact avram_gbB129_bounded_measurable_squared_difference_integrable
      ν (fun b => f (a, b)) (fun b => g (a, b))
      (hf.comp hpair) (hg.comp hpair) B hB
      (fun b => hfb (a, b)) (fun b => hgb (a, b))
  · exact avram_gbB132_bounded_joint_measurable_squared_error_outer_integrable
      μ ν f g hf hg B hB hfb hgb
