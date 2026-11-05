-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_public_large_small_original_jump_translation_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:13:55.607207+00:00
-- url     : https://prove2.me/submissions/44e09955-5a03-4214-9d37-070a872e59c8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open scoped BigOperators
/-- Split jump-grid translation errors into finitely marked cells (controlled by
the continuous mesh step) and the remaining small jump-mass cells. -/
theorem solution
    (n : ℕ) (S : Finset ℕ) (f : ℝ → ℝ)
    (r z c j : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hr : ∀ i, i < n → 0 ≤ r i ∧ r i ≤ 1)
    (hlarge : ∀ i, i < n → i ∈ S →
      |f (z i + c i - j i) - f (z i - j i)| ≤ K * |c i| ∧
      |f (z i + c i) - f (z i)| ≤ K * |c i|)
    (hsmall : ∀ i, i < n → i ∉ S →
      |f (z i + c i - j i) - f (z i + c i)| ≤ K * |j i| ∧
      |f (z i - j i) - f (z i)| ≤ K * |j i|) :
    |∑ i ∈ Finset.range n,
      r i * ((f (z i + c i - j i) - f (z i + c i)) -
        (f (z i - j i) - f (z i)))| ≤
      2 * K * (∑ i ∈ Finset.range n,
        if i ∈ S then |c i| else |j i|) := by
  classical
  have hcell (i : ℕ) (hi : i < n) :
      |(f (z i + c i - j i) - f (z i + c i)) -
        (f (z i - j i) - f (z i))| ≤
      2 * K * (if i ∈ S then |c i| else |j i|) := by
    by_cases hs : i ∈ S
    · rw [if_pos hs]
      have h := hlarge i hi hs
      have heq :
          (f (z i + c i - j i) - f (z i + c i)) -
              (f (z i - j i) - f (z i)) =
            (f (z i + c i - j i) - f (z i - j i)) -
              (f (z i + c i) - f (z i)) := by ring
      rw [heq]
      calc
        |(f (z i + c i - j i) - f (z i - j i)) -
            (f (z i + c i) - f (z i))| ≤
          |f (z i + c i - j i) - f (z i - j i)| +
            |f (z i + c i) - f (z i)| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le
                (f (z i + c i - j i) - f (z i - j i))
                (-(f (z i + c i) - f (z i))))
        _ ≤ K * |c i| + K * |c i| := add_le_add h.1 h.2
        _ = 2 * K * |c i| := by ring
    · rw [if_neg hs]
      have h := hsmall i hi hs
      calc
        |(f (z i + c i - j i) - f (z i + c i)) -
            (f (z i - j i) - f (z i))| ≤
          |f (z i + c i - j i) - f (z i + c i)| +
            |f (z i - j i) - f (z i)| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le
                (f (z i + c i - j i) - f (z i + c i))
                (-(f (z i - j i) - f (z i))))
        _ ≤ K * |j i| + K * |j i| := add_le_add h.1 h.2
        _ = 2 * K * |j i| := by ring
  calc
    |∑ i ∈ Finset.range n,
      r i * ((f (z i + c i - j i) - f (z i + c i)) -
        (f (z i - j i) - f (z i)))| ≤
      ∑ i ∈ Finset.range n,
        |r i * ((f (z i + c i - j i) - f (z i + c i)) -
          (f (z i - j i) - f (z i)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n,
      2 * K * (if i ∈ S then |c i| else |j i|) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hr i (Finset.mem_range.mp hi)).1]
      exact le_trans
        (mul_le_mul_of_nonneg_right
          (hr i (Finset.mem_range.mp hi)).2 (abs_nonneg _))
        (by simpa using hcell i (Finset.mem_range.mp hi))
    _ = 2 * K * (∑ i ∈ Finset.range n,
        if i ∈ S then |c i| else |j i|) := by
      rw [Finset.mul_sum]
