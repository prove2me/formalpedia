-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_count_pgf_pointwise_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:31:01.687468+00:00
-- url     : https://prove2.me/submissions/400aa3fb-35d5-4bca-b7b4-8d26e87f35e9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-! Bounds for the generating function of an arbitrary integer jump count. -/
theorem solution
    (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    1 - (1 - z) * (n : ℝ) ≤ z ^ n ∧
      z ^ n ≤ (if n = 0 then (1 : ℝ) else z) := by
  have hPow : ∀ m : ℕ, z ^ m ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hnonneg : 0 ≤ z ^ m := pow_nonneg hz0 m
        rw [pow_succ]
        nlinarith [mul_nonneg (sub_nonneg.mpr hz1) hnonneg]
  induction n with
  | zero => norm_num
  | succ m ih =>
      have hnonneg : 0 ≤ z ^ m := pow_nonneg hz0 m
      have hle : z ^ m ≤ 1 := hPow m
      have herror : 0 ≤ (1 - z) * (1 - z ^ m) :=
        mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr hle)
      constructor
      · have hprev := ih.1
        rw [pow_succ]
        push_cast
        nlinarith
      · simp only [Nat.succ_ne_zero, if_false]
        rw [pow_succ]
        nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hle)]