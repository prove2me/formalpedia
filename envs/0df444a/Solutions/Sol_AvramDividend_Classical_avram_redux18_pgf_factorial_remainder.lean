-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_pgf_factorial_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:25:23.830332+00:00
-- url     : https://prove2.me/submissions/86c9daa9-866b-4b5f-8171-0b8120231a83

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-! The generating-function error is bounded by the second factorial count. -/
theorem solution
    (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    0 ≤ z ^ n - (1 - (1 - z) * (n : ℝ)) ∧
    2 * (z ^ n - (1 - (1 - z) * (n : ℝ))) ≤
      (1 - z) ^ 2 * (n : ℝ) * ((n : ℝ) - 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hstep :
          z ^ (n + 1) - (1 - (1 - z) * ((n + 1 : ℕ) : ℝ)) =
            z * (z ^ n - (1 - (1 - z) * (n : ℝ))) +
              (1 - z) ^ 2 * (n : ℝ) := by
        rw [pow_succ, Nat.cast_succ]
        ring
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hd : 0 ≤ (1 - z) * (z ^ n - (1 - (1 - z) * (n : ℝ))) :=
        mul_nonneg (sub_nonneg.mpr hz1) ih.1
      constructor
      · rw [hstep]
        nlinarith [mul_nonneg hz0 ih.1,
          mul_nonneg (sq_nonneg (1 - z)) hn]
      · rw [hstep]
        push_cast
        nlinarith [ih.2, hd]
