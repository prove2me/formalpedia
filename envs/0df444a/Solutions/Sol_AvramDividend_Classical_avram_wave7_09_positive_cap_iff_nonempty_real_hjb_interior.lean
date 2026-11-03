-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_positive_cap_iff_nonempty_real_hjb_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:40:04.41327+00:00
-- url     : https://prove2.me/submissions/f60a2eef-8a4d-4c38-8e5f-d7130a1f3fc3

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The exact real HJB verification region is inhabited precisely when
the canonical ENNReal reserve cap is strictly positive. -/
theorem solution (C : ℝ≥0∞) :
    (∃ y : ℝ, 0 < y ∧ ENNReal.ofReal y < C) ↔ 0 < C := by
  constructor
  · rintro ⟨y, hypos, hyC⟩
    exact lt_of_le_of_lt bot_le hyC
  · intro hC
    by_cases hTop : C = ⊤
    · refine ⟨1, by norm_num, ?_⟩
      simp [hTop]
    · have hcReal : 0 < C.toReal :=
        ENNReal.toReal_pos (ne_of_gt hC) hTop
      have hHalfPos : 0 < C.toReal / 2 := by linarith
      have hHalfLt : C.toReal / 2 < C.toReal := by linarith
      refine ⟨C.toReal / 2, hHalfPos, ?_⟩
      have hBefore :
          ENNReal.ofReal (C.toReal / 2) < ENNReal.ofReal C.toReal :=
        (ENNReal.ofReal_lt_ofReal_iff hcReal).mpr hHalfLt
      simpa only [ENNReal.ofReal_toReal hTop] using hBefore
