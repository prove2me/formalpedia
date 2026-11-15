-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB76_original_interior_caplinear_value_exact_minplus_positive_part
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:36:22.614891+00:00
-- url     : https://prove2.me/submissions/c2633c41-89e0-41bd-afab-6d4dc78e0c14

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
noncomputable section

theorem solution
    (w : ℝ → ℝ) (b y : ℝ) :
    (if y ≤ b then w y else w b + (y - b)) =
      w (min y b) + max (y - b) 0 := by
  by_cases h : y ≤ b
  · rw [if_pos h, min_eq_left h]
    rw [max_eq_right (sub_nonpos.mpr h)] <;> ring
  · have hb : b ≤ y := le_of_lt (lt_of_not_ge h)
    rw [if_neg h, min_eq_right hb]
    rw [max_eq_left (sub_nonneg.mpr hb)] <;> ring
