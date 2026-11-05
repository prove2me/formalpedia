-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_assist_p3_finite_cap_extension_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:27:15.878664+00:00
-- url     : https://prove2.me/submissions/cadb5ee6-c659-4323-8903-5223675eee7b

import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal
noncomputable section

/-- Extending an already cap-extended value produces the same value. -/
theorem solution
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (w V : ℝ → ℝ)
    (hV : ∀ z : ℝ, V z =
      if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)) :
    ∀ z : ℝ, V z =
      if z ≤ C.toReal then V z
      else V C.toReal + (z - C.toReal) := by
  intro z
  by_cases hz : z ≤ C.toReal
  · rw [if_pos hz]
  · have hcap : V C.toReal = w C.toReal := by
      simpa only [if_pos (le_refl C.toReal)] using hV C.toReal
    rw [if_neg hz, hV z, if_neg hz, hcap]
