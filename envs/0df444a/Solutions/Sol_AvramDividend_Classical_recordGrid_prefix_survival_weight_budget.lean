-- Prove2me | solution 1 for AvramDividend.Classical.recordGrid_prefix_survival_weight_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:31:42.41917+00:00
-- url     : https://prove2.me/submissions/fd5235d7-dd72-436c-ada6-f5aa9a0779ca

import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal BigOperators

/-! Surviving final records give the full prefix; failed records contribute zero. -/
theorem solution
    (T : ℕ → ℝ≥0∞) (hT : Monotone T)
    (τ : ℝ≥0∞) (f : ℕ → ℝ≥0∞) (C : ℝ≥0∞)
    (hprefix : ∀ N : ℕ, T N < τ →
      (∑ n ∈ Finset.range N, f n) ≤ C) :
    ∀ N : ℕ,
      (∑ n ∈ Finset.range N,
        if T (n + 1) < τ then f n else 0) ≤ C := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    by_cases h : T (N + 1) < τ
    · calc
        (∑ n ∈ Finset.range (N + 1),
          if T (n + 1) < τ then f n else 0) =
          (∑ n ∈ Finset.range (N + 1), f n) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hle : n + 1 ≤ N + 1 :=
              Nat.succ_le_succ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
            exact if_pos (lt_of_le_of_lt (hT hle) h)
        _ ≤ C := hprefix (N + 1) h
    · simpa [Finset.sum_range_succ, h] using ih
