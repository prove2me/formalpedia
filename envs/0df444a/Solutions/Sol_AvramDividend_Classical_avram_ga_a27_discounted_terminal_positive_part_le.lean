-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a27_discounted_terminal_positive_part_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:29:47.046063+00:00
-- url     : https://prove2.me/submissions/a5fa12ff-05d7-4bc4-bc52-866bccac17b9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
noncomputable section

theorem solution
    (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) (a b : ℝ) :
    max (Real.exp (-(q * (t : ℝ))) * (a - b)) 0 ≤
      max a 0 + max (-b) 0 := by
  have ht : 0 ≤ (t : ℝ) := by positivity
  have hE0 : 0 ≤ Real.exp (-(q * (t : ℝ))) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hq ht])
  have hsum : a - b ≤ max a 0 + max (-b) 0 := by
    have h1 := le_max_left a 0
    have h2 := le_max_left (-b) 0
    linarith
  have hnon : 0 ≤ max a 0 + max (-b) 0 :=
    add_nonneg (le_max_right a 0) (le_max_right (-b) 0)
  by_cases hd : 0 ≤ a - b
  · have hp : 0 ≤ Real.exp (-(q * (t : ℝ))) * (a - b) :=
      mul_nonneg hE0 hd
    rw [max_eq_left hp]
    have hsmall : Real.exp (-(q * (t : ℝ))) * (a - b) ≤ a - b := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hE1) hd]
    linarith
  · have hn : a - b ≤ 0 := le_of_lt (lt_of_not_ge hd)
    have hp : Real.exp (-(q * (t : ℝ))) * (a - b) ≤ 0 := by
      nlinarith [mul_nonneg hE0 (neg_nonneg.mpr hn)]
    rw [max_eq_right hp]
    exact hnon
