-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_actual_finset_step_jump_equals_source_mark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:46:25.635075+00:00
-- url     : https://prove2.me/submissions/f57d727c-e615-430f-98d2-dd886619172e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_marked_step_jump_eq_marks_at_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (S : Finset ℝ≥0) (t : ℝ≥0)
    (ht : t ∈ S) :
    Finset.sum S (fun u => if u ≤ t then
        Function.leftLim f u - f u else 0) -
      Finset.sum S (fun u => if u < t then
        Function.leftLim f u - f u else 0) =
      Function.leftLim f t - f t := by
  have h := finite_marked_step_jump_eq_marks_at_time
    S (fun u : ℝ≥0 => u) (fun u => Function.leftLim f u - f u) t
  simpa [ht] using h
