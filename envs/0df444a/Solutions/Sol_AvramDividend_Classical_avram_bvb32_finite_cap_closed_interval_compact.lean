-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb32_finite_cap_closed_interval_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:15:21.410895+00:00
-- url     : https://prove2.me/submissions/a305439b-ce65-4bf7-af7b-0999ee078088

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤) :
    IsCompact {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} := by
  have hEq :
      {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} =
        Set.Icc (0 : ℝ) C.toReal := by
    ext b
    constructor
    · rintro ⟨h0, hC⟩
      exact ⟨h0, (ENNReal.ofReal_le_iff_le_toReal hFinite).mp hC⟩
    · rintro ⟨h0, hC⟩
      exact ⟨h0, (ENNReal.ofReal_le_iff_le_toReal hFinite).mpr hC⟩
  rw [hEq]
  exact isCompact_Icc
