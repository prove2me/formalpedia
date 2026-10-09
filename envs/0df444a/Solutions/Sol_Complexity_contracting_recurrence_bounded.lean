-- Prove2me | solution 1 for Complexity.contracting_recurrence_bounded
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T08:49:23.696574+00:00
-- url     : https://prove2.me/submissions/97219a76-d9b5-4c5b-bb1d-c44ee4f1160e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

theorem solution (f : ℕ → ℝ) (a N : ℕ) (q A : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hrec : ∀ n : ℕ, N ≤ n → a ≤ n →
      ∃ m : ℕ, a ≤ m ∧ m < n ∧ f n ≤ q * f m + A) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, a ≤ n → f n ≤ C := by
  classical
  let B : ℝ := ∑ k ∈ Finset.range N, |f k|
  let C : ℝ := max (max B (A / (1 - q))) 1
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCB : B ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCA : A / (1 - q) ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hA : A ≤ (1 - q) * C := by
    have := (div_le_iff₀ (by linarith : 0 < 1 - q)).1 hCA
    nlinarith
  refine ⟨C, by linarith, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hsmall : n < N
    · have hbase : |f n| ≤ B :=
        Finset.single_le_sum (fun k _ => abs_nonneg (f k)) (Finset.mem_range.mpr hsmall)
      exact (le_abs_self (f n)).trans (hbase.trans hCB)
    · obtain ⟨m, hm, hmn, hstep⟩ := hrec n (by omega) hn
      have hfm := ih m hmn hm
      have hmul := mul_le_mul_of_nonneg_left hfm hq0
      nlinarith
