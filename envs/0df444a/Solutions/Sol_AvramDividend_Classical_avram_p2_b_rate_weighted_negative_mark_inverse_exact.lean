-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_weighted_negative_mark_inverse_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:50:03.035751+00:00
-- url     : https://prove2.me/submissions/76700bc1-59c5-4421-98a1-4b72f9541712

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution (f : ℝ → ℝ) (y : ℝ) (hy : y < 0) :
    (Real.exp y - 1) ^ 4 *
      (f (Real.log (Real.exp y)) / (Real.exp y - 1) ^ 4) = f y := by
  rw [Real.log_exp]
  have hlt : Real.exp y < 1 := by
    calc
      Real.exp y < Real.exp 0 := Real.exp_lt_exp.mpr hy
      _ = 1 := Real.exp_zero
  have hnonzero : Real.exp y - 1 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt hlt)
  field_simp [hnonzero]
