-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:50:48.926923+00:00
-- url     : https://prove2.me/submissions/4790ec6b-496d-491a-852c-8b174a279ce1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (C : ℝ≥0∞) :
    IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  change IsOpen (Ioi (0 : ℝ) ∩
    (fun y : ℝ => ENNReal.ofReal y) ⁻¹' Iio C)
  exact isOpen_Ioi.inter
    (isOpen_Iio.preimage ENNReal.continuous_ofReal)
