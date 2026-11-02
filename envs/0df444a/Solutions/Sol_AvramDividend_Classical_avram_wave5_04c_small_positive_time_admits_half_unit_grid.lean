-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_small_positive_time_admits_half_unit_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:29:40.971724+00:00
-- url     : https://prove2.me/submissions/6e3c2b10-b70f-4566-9b94-feda4416dd71

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open scoped NNReal

theorem solution (h : ℝ) (hh : 0 < h) (hhalf : h ≤ 1 / 2) :
    ∃ n : ℕ, (1 / 2 : ℝ) ≤ (n : ℝ) * h ∧ (n : ℝ) * h ≤ 1 := by
  let n : ℕ := ⌊1 / h⌋₊
  have hp : 0 ≤ (1 / h : ℝ) := by positivity
  have hflo : (n : ℝ) ≤ 1 / h := Nat.floor_le hp
  have hfhi : 1 / h < (n : ℝ) + 1 := Nat.lt_floor_add_one (1 / h)
  have hcancel : (1 / h) * h = (1 : ℝ) := by
    field_simp
  have hlo : 1 - h < (n : ℝ) * h := by
    have hm := mul_lt_mul_of_pos_right hfhi hh
    nlinarith
  have hhi : (n : ℝ) * h ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hflo (le_of_lt hh)
    nlinarith
  refine ⟨n, ?_, hhi⟩
  linarith
