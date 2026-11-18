-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_grid_step_small_of_16000_times_n_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T22:00:40.807184+00:00
-- url     : https://prove2.me/submissions/3754fa7e-cd43-427b-aa51-4be7f3c13c98

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section
/-- Explicit original physical mesh tail step bound. -/
theorem solution
    (n m : ℕ) (hm : 16000 * n ≤ m + 1) :
    (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0) ≤ (1 / 16000 : ℝ≥0) := by
  have hd : (0 : ℝ≥0) < ((m + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.succ_pos m
  apply (div_le_iff₀ hd).2
  have hm' : (16000 : ℝ≥0) * (n : ℝ≥0) ≤
      ((m + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast hm
  have hRecip : (1 / 16000 : ℝ≥0) *
      (16000 : ℝ≥0) = 1 := by norm_num
  calc
    (n : ℝ≥0) = (1 : ℝ≥0) * (n : ℝ≥0) :=
      (one_mul _).symm
    _ = ((1 / 16000 : ℝ≥0) * 16000) *
        (n : ℝ≥0) := by rw [hRecip]
    _ = (1 / 16000 : ℝ≥0) *
        (16000 * (n : ℝ≥0)) :=
      mul_assoc _ _ _
    _ ≤ (1 / 16000 : ℝ≥0) *
        (((m + 1 : ℕ) : ℝ≥0)) :=
      mul_le_mul_of_nonneg_left hm' (by norm_num)
