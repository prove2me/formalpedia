-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_public_weighted_source_jump_taylor_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:08:46.600841+00:00
-- url     : https://prove2.me/submissions/f9685d32-668f-466f-ac32-3d83bb14e5fe

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-- A finite-grid BV Taylor bound that keeps the source jump increment exact.
Only the continuous (jump-removed) part is linearised. -/
theorem solution
    (f : ℝ → ℝ) (n : ℕ)
    (r z cont jump delta : ℕ → ℝ)
    (ε B : ℝ) (hε : 0 ≤ ε)
    (hstep : ∀ i, i < n → delta i = cont i - jump i)
    (hr : ∀ i, i < n → 0 ≤ r i ∧ r i ≤ 1)
    (htaylor : ∀ i, i < n →
      |f (z i + cont i) - f (z i) - deriv f (z i) * cont i| ≤
        ε * |cont i|)
    (hvar : (∑ i ∈ Finset.range n, |cont i|) ≤ B) :
    |∑ i ∈ Finset.range n,
      r i * ((f (z i + delta i) - f (z i)) -
        (f (z i + cont i - jump i) - f (z i + cont i)) -
        deriv f (z i) * cont i)| ≤ ε * B := by
  classical
  have hcell (i : ℕ) (hi : i < n) :
      ((f (z i + delta i) - f (z i)) -
        (f (z i + cont i - jump i) - f (z i + cont i)) -
        deriv f (z i) * cont i) =
          f (z i + cont i) - f (z i) -
            deriv f (z i) * cont i := by
    rw [hstep i hi]
    ring
  have hpoint (i : ℕ) (hi : i < n) :
      |r i * ((f (z i + delta i) - f (z i)) -
        (f (z i + cont i - jump i) - f (z i + cont i)) -
        deriv f (z i) * cont i)| ≤ ε * |cont i| := by
    rw [hcell i hi, abs_mul, abs_of_nonneg (hr i hi).1]
    calc
      r i * |f (z i + cont i) - f (z i) -
          deriv f (z i) * cont i| ≤
          1 * |f (z i + cont i) - f (z i) -
            deriv f (z i) * cont i| :=
        mul_le_mul_of_nonneg_right (hr i hi).2 (abs_nonneg _)
      _ = |f (z i + cont i) - f (z i) -
          deriv f (z i) * cont i| := one_mul _
      _ ≤ ε * |cont i| := htaylor i hi
  calc
    |∑ i ∈ Finset.range n,
      r i * ((f (z i + delta i) - f (z i)) -
        (f (z i + cont i - jump i) - f (z i + cont i)) -
        deriv f (z i) * cont i)| ≤
        ∑ i ∈ Finset.range n,
          |r i * ((f (z i + delta i) - f (z i)) -
            (f (z i + cont i - jump i) - f (z i + cont i)) -
            deriv f (z i) * cont i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, ε * |cont i| := by
      apply Finset.sum_le_sum
      intro i hi
      exact hpoint i (Finset.mem_range.mp hi)
    _ = ε * ∑ i ∈ Finset.range n, |cont i| := by
      rw [Finset.mul_sum]
    _ ≤ ε * B := mul_le_mul_of_nonneg_left hvar hε
