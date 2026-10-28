-- Prove2me | solution 1 for AvramDividend.Classical.filtered_surviving_Ioc_prefixes_directed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:52:17.871046+00:00
-- url     : https://prove2.me/submissions/eb685169-130e-4a76-b2f2-4ebfc36b180c

import Mathlib.Data.ENNReal.Real
open Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Surviving positive-time initial intervals, with invalid endpoints
contributing empty sets, are ordered by inclusion up to a common interval. -/
theorem solution
    (σ : ℝ≥0∞) (grid : ℕ → ℝ≥0) :
    Directed (fun (a b : Set ℝ) => a ⊆ b)
      (fun n : ℕ => {x : ℝ | 0 < x ∧ x ≤ (grid n : ℝ) ∧ (grid n : ℝ≥0∞) < σ}) := by
  intro i j
  by_cases hi : (grid i : ℝ≥0∞) < σ
  · by_cases hj : (grid j : ℝ≥0∞) < σ
    · rcases le_total (grid i : ℝ) (grid j : ℝ) with hij | hji
      · refine ⟨j, ?_, ?_⟩
        · intro x hx
          exact ⟨hx.1, le_trans hx.2.1 hij, hj⟩
        · intro x hx
          exact hx
      · refine ⟨i, ?_, ?_⟩
        · intro x hx
          exact hx
        · intro x hx
          exact ⟨hx.1, le_trans hx.2.1 hji, hi⟩
    · refine ⟨i, ?_, ?_⟩
      · intro x hx
        exact hx
      · intro x hx
        exact False.elim (hj hx.2.2)
  · refine ⟨j, ?_, ?_⟩
    · intro x hx
      exact False.elim (hi hx.2.2)
    · intro x hx
      exact hx
