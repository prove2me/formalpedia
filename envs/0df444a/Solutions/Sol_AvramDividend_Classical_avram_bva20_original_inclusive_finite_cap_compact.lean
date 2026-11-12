-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_original_inclusive_finite_cap_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:34:18.619189+00:00
-- url     : https://prove2.me/submissions/5c79c9dd-c7b1-42d1-b4b7-9317f13c8c85

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A finite inclusive original reserve cap is a compact interval. -/
theorem solution
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤) :
    IsCompact {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} := by
  have hSet :
      {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} =
        Icc (0 : ℝ) C.toReal := by
    ext b
    simp only [mem_setOf_eq, mem_Icc]
    constructor
    · rintro ⟨hb, hbC⟩
      exact ⟨hb, (ENNReal.ofReal_le_iff_le_toReal hFinite).mp hbC⟩
    · rintro ⟨hb, hbC⟩
      exact ⟨hb, (ENNReal.ofReal_le_iff_le_toReal hFinite).mpr hbC⟩
  rw [hSet]
  exact isCompact_Icc
