-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB218_bounded_joint_mesh_L2_limit_implies_nested_pair_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:37:15.445289+00:00
-- url     : https://prove2.me/submissions/3dee4341-6775-4235-aa77-564b06cf483e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB138_bounded_joint_measurable_pair_nested_squared_integrable
import Theorems.Thm_AvramDividend_Classical_avram_gbB217_nested_L2_one_mesh_implies_two_mesh_cauchy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : ℕ → α → β → ℝ) (g : α → β → ℝ)
    (hf : ∀ m, Measurable (fun z : α × β => f m z.1 z.2))
    (hg : Measurable (fun z : α × β => g z.1 z.2))
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ m a b, |f m a b| ≤ B)
    (hgb : ∀ a b, |g a b| ≤ B)
    (hlim : Tendsto (fun m =>
      ∫ a, (∫ b, (f m a b - g a b)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun mp : ℕ × ℕ =>
      ∫ a, (∫ b, (f mp.1 a b - f mp.2 a b)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  have hFG (m : ℕ) :=
    avram_gbB138_bounded_joint_measurable_pair_nested_squared_integrable
      μ ν (fun z : α × β => f m z.1 z.2)
      (fun z : α × β => g z.1 z.2)
      (hf m) hg B hB
      (fun z => hfb m z.1 z.2)
      (fun z => hgb z.1 z.2)
  have hFF (m p : ℕ) :=
    avram_gbB138_bounded_joint_measurable_pair_nested_squared_integrable
      μ ν (fun z : α × β => f m z.1 z.2)
      (fun z : α × β => f p z.1 z.2)
      (hf m) (hf p) B hB
      (fun z => hfb m z.1 z.2)
      (fun z => hfb p z.1 z.2)
  exact avram_gbB217_nested_L2_one_mesh_implies_two_mesh_cauchy
    μ ν f g (fun m t => (hFG m).1 t)
    (fun m p t => (hFF m p).1 t)
    (fun m => (hFG m).2)
    (fun m p => (hFF m p).2) hlim

