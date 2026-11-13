-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a30_horizon_final_cell_left_strict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:37:38.06721+00:00
-- url     : https://prove2.me/submissions/a414523e-dca7-46ec-ab22-11aee69e4ad6

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section

theorem solution
    (n : ℝ≥0) (hn : 0 < n) (m : ℕ) :
    (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1)) < n := by
  have hden : 0 < (m : ℝ≥0) + 1 := by positivity
  have hm : (m : ℝ≥0) < (m : ℝ≥0) + 1 := by exact_mod_cast Nat.lt_succ_self m
  have hratio : (m : ℝ≥0) / ((m : ℝ≥0) + 1) < 1 :=
    (div_lt_one hden).2 hm
  calc
    (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1)) =
        n * ((m : ℝ≥0) / ((m : ℝ≥0) + 1)) := by
      simp only [div_eq_mul_inv]
      ring
    _ < n * 1 := mul_lt_mul_of_pos_left hratio hn
    _ = n := mul_one n
