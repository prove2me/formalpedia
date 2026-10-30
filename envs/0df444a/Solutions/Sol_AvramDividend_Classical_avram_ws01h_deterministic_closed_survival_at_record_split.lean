-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_deterministic_closed_survival_at_record_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:31:13.545569+00:00
-- url     : https://prove2.me/submissions/9da73bc3-8f09-4f2c-b345-08a293e5b4a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal

/-- Splitting every nonnegative-reserve observation at an actual finite record
is an exact equivalence of closed survival events and shifted future survival. -/
theorem solution
    (f : ℝ≥0 → ℝ) (x : ℝ) (τ t : ℝ≥0)
    (hτt : τ ≤ t) :
    (∀ s : ℝ≥0, s ≤ t → 0 ≤ x + f s) ↔
      (∀ s : ℝ≥0, s ≤ τ → 0 ≤ x + f s) ∧
      (∀ u : ℝ≥0, u ≤ t - τ →
        0 ≤ (x + f τ) + (f (τ + u) - f τ)) := by
  constructor
  · intro h
    constructor
    · intro s hs
      exact h s (hs.trans hτt)
    · intro u hu
      have hsum : τ + (t - τ) = t := by
        rw [add_comm]
        exact tsub_add_cancel_of_le hτt
      have hle : τ + u ≤ t := by
        calc
          τ + u ≤ τ + (t - τ) := add_le_add_right hu τ
          _ = t := hsum
      have hz := h (τ + u) hle
      linarith
  · rintro ⟨hpre, hpost⟩ s hs
    by_cases hsτ : s ≤ τ
    · exact hpre s hsτ
    · have hτs : τ ≤ s := le_of_not_ge hsτ
      have hsub : s - τ ≤ t - τ := tsub_le_tsub_right hs τ
      have hsum : τ + (s - τ) = s := by
        rw [add_comm]
        exact tsub_add_cancel_of_le hτs
      have hz := hpost (s - τ) hsub
      rw [hsum] at hz
      linarith
