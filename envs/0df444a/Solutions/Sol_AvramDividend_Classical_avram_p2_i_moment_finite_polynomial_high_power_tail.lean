-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_finite_polynomial_high_power_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:40:43.381887+00:00
-- url     : https://prove2.me/submissions/b74c3fcd-e8b0-4c10-a390-43f699f7963e

import Mathlib
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

theorem solution
    (s : Finset ℕ) (a : ℕ → ℝ) (n r : ℕ)
    (hs : ∀ j ∈ s, j ≤ n) (z : ℝ) (hz : 2 ≤ z) :
    (2 : ℝ) ^ r * |∑ j ∈ s, a j * z ^ j| ≤
      (∑ j ∈ s, |a j|) * z ^ (n + r) := by
  have hz0 : 0 ≤ z := by linarith
  have hz1 : 1 ≤ z := by linarith
  have hstep (t : ℕ) : z ^ t ≤ z ^ (t + 1) := by
    rw [pow_succ]
    nlinarith [mul_nonneg (pow_nonneg hz0 t) (sub_nonneg.mpr hz1)]
  have hpow (j : ℕ) (hj : j ∈ s) : z ^ j ≤ z ^ n := by
    exact Nat.le_induction (le_refl (z ^ j))
      (fun m hm ih => le_trans ih (hstep m)) n (hs j hj)
  have hterm (j : ℕ) (hj : j ∈ s) :
      |a j * z ^ j| ≤ |a j| * z ^ n := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
    exact mul_le_mul_of_nonneg_left (hpow j hj) (abs_nonneg _)
  have hsum :
      |∑ j ∈ s, a j * z ^ j| ≤
        (∑ j ∈ s, |a j|) * z ^ n := by
    calc
      |∑ j ∈ s, a j * z ^ j| ≤
          ∑ j ∈ s, |a j * z ^ j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, |a j| * z ^ n := by
        apply Finset.sum_le_sum
        intro j hj
        exact hterm j hj
      _ = (∑ j ∈ s, |a j|) * z ^ n := by rw [Finset.sum_mul]
  have hr : (2 : ℝ) ^ r * z ^ n ≤ z ^ (n + r) := by
    have hzr : (2 : ℝ) ^ r ≤ z ^ r := by gcongr
    calc
      (2 : ℝ) ^ r * z ^ n ≤ z ^ r * z ^ n :=
        mul_le_mul_of_nonneg_right hzr (pow_nonneg hz0 n)
      _ = z ^ (n + r) := by rw [pow_add]; ring
  have hC : 0 ≤ ∑ j ∈ s, |a j| :=
    Finset.sum_nonneg (by intro j hj; exact abs_nonneg _)
  calc
    (2 : ℝ) ^ r * |∑ j ∈ s, a j * z ^ j| ≤
        (2 : ℝ) ^ r * ((∑ j ∈ s, |a j|) * z ^ n) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (∑ j ∈ s, |a j|) * ((2 : ℝ) ^ r * z ^ n) := by ring
    _ ≤ (∑ j ∈ s, |a j|) * z ^ (n + r) :=
      mul_le_mul_of_nonneg_left hr hC
