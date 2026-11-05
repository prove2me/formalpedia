-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_assist_p3_self_cap_crossing_correction_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:27:50.178652+00:00
-- url     : https://prove2.me/submissions/97525498-1eef-4cf0-9202-d0b08966d78d

import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal
noncomputable section

/-- The original physical grid's κ-term vanishes for the extended value. -/
theorem solution
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (p : ℝ) :
    (if C = ⊤ then 0
     else if p ≤ C.toReal then 0
     else V C.toReal + (p - C.toReal) - V p) = 0 := by
  by_cases hC : C = ⊤
  · simp [hC]
  · by_cases hp : p ≤ C.toReal
    · simp [hC, hp]
    · have hcap : V C.toReal = w C.toReal := by
        simpa only [if_pos (le_refl C.toReal)] using hVfinite hC C.toReal
      have hpV : V p = w C.toReal + (p - C.toReal) := by
        simpa only [if_neg hp] using hVfinite hC p
      simp only [if_neg hC, if_neg hp]
      rw [hcap, hpV]
      ring
