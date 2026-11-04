-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_ordered_cells_three_case_frequently
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:47:47.417748+00:00
-- url     : https://prove2.me/submissions/0bc93122-bc8d-4ac2-8232-fca5d44ae3e0

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- Ordered shrinking-cell endpoints cannot avoid all three relative
positions with respect to a fixed candidate accumulation time. -/
theorem solution
    (a b : ℕ → ℝ≥0) (t : ℝ≥0)
    (hab : ∀ n, a n ≤ b n) :
    (∃ᶠ n in atTop, b n < t) ∨
    (∃ᶠ n in atTop, t ≤ a n) ∨
    (∃ᶠ n in atTop, a n < t ∧ t ≤ b n) := by
  classical
  by_contra h
  have h1 : ¬ (∃ᶠ n in atTop, b n < t) := by
    tauto
  have h2 : ¬ (∃ᶠ n in atTop, t ≤ a n) := by
    tauto
  have h3 : ¬ (∃ᶠ n in atTop, a n < t ∧ t ≤ b n) := by
    tauto
  have e1 : ∀ᶠ n in atTop, ¬ b n < t :=
    Filter.not_frequently.mp h1
  have e2 : ∀ᶠ n in atTop, ¬ t ≤ a n :=
    Filter.not_frequently.mp h2
  have e3 : ∀ᶠ n in atTop, ¬ (a n < t ∧ t ≤ b n) :=
    Filter.not_frequently.mp h3
  have ef : ∀ᶠ n in (atTop : Filter ℕ), False := by
    filter_upwards [e1, e2, e3] with n hn1 hn2 hn3
    have hbn : t ≤ b n := le_of_not_gt hn1
    have han : a n < t := lt_of_not_ge hn2
    exact hn3 ⟨han, hbn⟩
  obtain ⟨n, hn⟩ := ef.exists
  exact hn
