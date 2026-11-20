-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_nonpositive_ruinreserve_caplinear_value_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:35:54.712032+00:00
-- url     : https://prove2.me/submissions/b49673d7-3477-4a33-bb8d-336ab56b85d0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (z : ℝ) (hz : z ≤ 0) :
    0 ≤ (if ENNReal.ofReal z ≤ C then w z
         else w C.toReal + (z - C.toReal)) := by
  have hz0 : ENNReal.ofReal z = 0 := ENNReal.ofReal_eq_zero.mpr hz
  have hzC : ENNReal.ofReal z ≤ C := by simp [hz0]
  rw [if_pos hzC]
  rcases lt_or_eq_of_le hz with hlt | heq
  · rw [hw_neg z hlt]
  · subst z
    exact hw0
