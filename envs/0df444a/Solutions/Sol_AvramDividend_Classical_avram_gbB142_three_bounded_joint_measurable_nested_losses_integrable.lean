-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB142_three_bounded_joint_measurable_nested_losses_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:45:41.313296+00:00
-- url     : https://prove2.me/submissions/1f5b2f17-061b-461b-ab2b-6b3e0c10178b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB138_bounded_joint_measurable_pair_nested_squared_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
noncomputable section
theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f g h : α × β → ℝ) (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (B : ℝ) (hB : 0 ≤ B) (hfb : ∀ z, |f z| ≤ B)
    (hgb : ∀ z, |g z| ≤ B) (hhb : ∀ z, |h z| ≤ B) :
    (∀ a, Integrable (fun b => (f (a,b)-g (a,b))^2) ν ∧
          Integrable (fun b => (f (a,b)-h (a,b))^2) ν ∧
          Integrable (fun b => (h (a,b)-g (a,b))^2) ν) ∧
    Integrable (fun a => ∫ b, (f (a,b)-g (a,b))^2 ∂ν) μ ∧
    Integrable (fun a => ∫ b, (f (a,b)-h (a,b))^2 ∂ν) μ ∧
    Integrable (fun a => ∫ b, (h (a,b)-g (a,b))^2 ∂ν) μ := by
  rcases avram_gbB138_bounded_joint_measurable_pair_nested_squared_integrable
    μ ν f g hf hg B hB hfb hgb with ⟨hfg,hfgO⟩
  rcases avram_gbB138_bounded_joint_measurable_pair_nested_squared_integrable
    μ ν f h hf hh B hB hfb hhb with ⟨hfh,hfhO⟩
  rcases avram_gbB138_bounded_joint_measurable_pair_nested_squared_integrable
    μ ν h g hh hg B hB hhb hgb with ⟨hhg,hhgO⟩
  exact ⟨fun a => ⟨hfg a,hfh a,hhg a⟩,hfgO,hfhO,hhgO⟩
