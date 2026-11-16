-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_finite_compensated_residual_left_right_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:50:46.955798+00:00
-- url     : https://prove2.me/submissions/5bb63ee9-1dac-432b-a7d6-a0eaee584668

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_actual_finset_step_jump_equals_source_mark
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (drift : ℝ)
    (S : Finset ℝ≥0) (t : ℝ≥0) (ht : t ∈ S) :
    (t : ℝ) * drift - f t -
      Finset.sum S (fun u => if u ≤ t then Function.leftLim f u - f u else 0) =
    (t : ℝ) * drift - Function.leftLim f t -
      Finset.sum S (fun u => if u < t then Function.leftLim f u - f u else 0) := by
  have h := avram_bva_actual_finset_step_jump_equals_source_mark f S t ht
  linarith
