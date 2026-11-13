-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a26_clipped_last_times_equal_after_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:11:15.58151+00:00
-- url     : https://prove2.me/submissions/0391539e-fd9b-497c-b206-be00eafd7b0a

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section

theorem solution (n : ℝ≥0) (m : ℕ) (r : ℝ≥0)
    (hstop : r ≤ (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1))) :
    min ((m : ℝ≥0) * (n / ((m : ℝ≥0) + 1))) r = r ∧
    min (((m + 1 : ℕ) : ℝ≥0) * (n / ((m : ℝ≥0) + 1))) r = r := by
  let δ : ℝ≥0 := n / ((m : ℝ≥0) + 1)
  have hcast : (m : ℝ≥0) ≤ ((m + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.le_succ m
  have hgrid : (m : ℝ≥0) * δ ≤ ((m + 1 : ℕ) : ℝ≥0) * δ :=
    mul_le_mul_of_nonneg_right hcast (by positivity)
  exact ⟨min_eq_right hstop, min_eq_right (hstop.trans hgrid)⟩
