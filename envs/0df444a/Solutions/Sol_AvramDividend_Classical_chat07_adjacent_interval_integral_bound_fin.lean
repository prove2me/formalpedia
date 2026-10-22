-- Prove2me | solution 1 for AvramDividend.Classical.chat07_adjacent_interval_integral_bound_fin
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-10-21T21:45:39.587739+00:00
-- url     : https://prove2.me/submissions/5ebaf493-8ce9-4135-b7bf-5fb3cb52e075

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory intervalIntegral
open scoped NNReal ENNReal

theorem solution
    (f g : ℝ → ℝ) (c : ℝ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hg : ∀ a b : ℝ, IntervalIntegrable g volume a b)
    (hstep : ∀ n : ℕ,
        (∫ x in (n : ℝ)..((n : ℝ) + 1), f x) ≤
          c * (∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), g x))
    (n : ℕ) :
    (∫ x in (0 : ℝ)..(n : ℝ), f x) ≤
      c * (∫ x in (1 : ℝ)..((n : ℝ) + 1), g x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∫ x in (0 : ℝ)..((n.succ : ℕ) : ℝ), f x) =
            (∫ x in (0 : ℝ)..(n : ℝ), f x) +
              (∫ x in (n : ℝ)..((n : ℝ) + 1), f x) :=
          by
            simpa [Nat.cast_succ] using
              (intervalIntegral.integral_add_adjacent_intervals
                (hf 0 (n : ℝ)) (hf (n : ℝ) ((n : ℝ) + 1))).symm
        _ ≤ c * (∫ x in (1 : ℝ)..((n : ℝ) + 1), g x) +
              c * (∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), g x) :=
          add_le_add ih (hstep n)
        _ = c * (∫ x in (1 : ℝ)..((n : ℝ) + 2), g x) := by
          rw [← mul_add,
            intervalIntegral.integral_add_adjacent_intervals
              (hg 1 ((n : ℝ) + 1))
              (hg ((n : ℝ) + 1) ((n : ℝ) + 2))]
        _ = c * (∫ x in (1 : ℝ)..(((n.succ : ℕ) : ℝ) + 1), g x) := by
          congr 2
          simp only [Nat.cast_succ]
          ring
