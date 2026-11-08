-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_bv_drift10_zero_extended_value_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:33:27.979203+00:00
-- url     : https://prove2.me/submissions/fa230cef-c686-4730-a94f-a26646ce3766

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ x : ℝ, x < 0 → w x = 0) (hwzero : w 0 = 0) :
    Continuous w := by
  have hcomp : Continuous (fun x : ℝ => w (max x 0)) := by
    apply ContinuousOn.comp_continuous hw_cont (continuous_id.max continuous_const)
    intro x
    exact le_max_right x 0
  have heq : w = (fun x : ℝ => w (max x 0)) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp [max_eq_left hx]
    · have hlt : x < 0 := lt_of_not_ge hx
      rw [hw_neg x hlt, max_eq_right (le_of_lt hlt), hwzero]
  rw [heq]
  exact hcomp
