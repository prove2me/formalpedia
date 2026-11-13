-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB148_measurable_fibre_squared_loss_integrable_with_time_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:18:39.764841+00:00
-- url     : https://prove2.me/submissions/1ef43418-e0ed-4400-9065-153eb1f399ba

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB129_bounded_measurable_squared_difference_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
noncomputable section

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν]
    (f g : α × β → ℝ) (hf : Measurable f) (hg : Measurable g)
    (Bf Bg : α → ℝ) (hBf : ∀ a, 0 ≤ Bf a) (hBg : ∀ a, 0 ≤ Bg a)
    (hfb : ∀ a b, |f (a,b)| ≤ Bf a)
    (hgb : ∀ a b, |g (a,b)| ≤ Bg a) :
    ∀ a, Integrable (fun b => (f (a,b) - g (a,b)) ^ 2) ν := by
  intro a
  let M : ℝ := max (Bf a) (Bg a)
  have hM : 0 ≤ M := (hBf a).trans (le_max_left _ _)
  have hp : Measurable (fun b : β => (a,b)) :=
    measurable_const.prodMk measurable_id
  exact avram_gbB129_bounded_measurable_squared_difference_integrable
    ν (fun b => f (a,b)) (fun b => g (a,b))
    (hf.comp hp) (hg.comp hp) M hM
    (fun b => (hfb a b).trans (le_max_left _ _))
    (fun b => (hgb a b).trans (le_max_right _ _))
