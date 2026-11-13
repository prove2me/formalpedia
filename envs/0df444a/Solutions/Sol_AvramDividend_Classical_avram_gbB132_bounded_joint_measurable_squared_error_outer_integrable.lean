-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB132_bounded_joint_measurable_squared_error_outer_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:02:54.272758+00:00
-- url     : https://prove2.me/submissions/63a4b8b7-7566-4516-9e11-c48ca7fccef4

import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_AvramDividend_Classical_avram_gbB129_bounded_measurable_squared_difference_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
noncomputable section

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f g : α × β → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ z, |f z| ≤ B) (hgb : ∀ z, |g z| ≤ B) :
    Integrable (fun a => ∫ b, (f (a, b) - g (a, b)) ^ 2 ∂ν) μ := by
  have hprod : Integrable (fun z => (f z - g z) ^ 2) (μ.prod ν) :=
    avram_gbB129_bounded_measurable_squared_difference_integrable
      (μ.prod ν) f g hf hg B hB hfb hgb
  exact hprod.integral_prod_left
