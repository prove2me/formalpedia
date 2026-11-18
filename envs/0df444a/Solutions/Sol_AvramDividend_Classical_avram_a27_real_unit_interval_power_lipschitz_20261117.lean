-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_real_unit_interval_power_lipschitz_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:37:34.233238+00:00
-- url     : https://prove2.me/submissions/213c02d8-3fe0-4b75-a650-c6c8e0960c7b

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

theorem solution
    (z w : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (n : ℕ) :
    |z ^ n - w ^ n| ≤ (n : ℝ) * |z - w| := by
  have hMaxNonneg : 0 ≤ max |z| |w| :=
    le_max_of_le_left (abs_nonneg z)
  have hMaxLe : max |z| |w| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg hz, abs_of_nonneg hw]
    exact max_le hz1 hw1
  have hPow : ∀ k : ℕ, (max |z| |w|) ^ k ≤ (1 : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      calc
        (max |z| |w|) ^ k * max |z| |w| ≤
            (max |z| |w|) ^ k * 1 := by
          exact mul_le_mul_of_nonneg_left hMaxLe (pow_nonneg hMaxNonneg _)
        _ = (max |z| |w|) ^ k := by ring
        _ ≤ 1 := ih
  calc
    |z ^ n - w ^ n| ≤
        |z - w| * (n : ℝ) * (max |z| |w|) ^ (n - 1) :=
          abs_pow_sub_pow_le z w n
    _ ≤ |z - w| * (n : ℝ) * 1 := by
      exact mul_le_mul_of_nonneg_left (hPow (n - 1))
        (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    _ = (n : ℝ) * |z - w| := by ring
