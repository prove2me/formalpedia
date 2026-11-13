-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a27_lindeberg_scalar_fourth_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:46:20.989543+00:00
-- url     : https://prove2.me/submissions/8b3d4b66-65e9-4506-b3ce-8dd3ca2a0575

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (r z : ℝ) (hr : 0 < r) :
    (if r ≤ |z| then z ^ 2 else 0) ≤ z ^ 4 / r ^ 2 := by
  split_ifs with h
  · have hrr : r ^ 2 ≤ z ^ 2 := by
      nlinarith [sq_abs z, abs_nonneg z]
    apply (le_div_iff₀ (sq_pos_of_pos hr)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hrr) (sq_nonneg z)]
  · positivity
