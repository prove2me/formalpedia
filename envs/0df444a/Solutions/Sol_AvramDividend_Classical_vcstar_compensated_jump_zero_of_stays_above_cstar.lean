-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_compensated_jump_zero_of_stays_above_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:31:37.597846+00:00
-- url     : https://prove2.me/submissions/2f3c6ff7-f0d2-4ed0-8536-8ba460c69d4f

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_linear_gt_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The compensated jump term vanishes whenever both endpoints remain
strictly above the optimal barrier, so only barrier-crossing jumps contribute. -/
theorem solution (W : ℝ → ℝ) (x z : ℝ)
    (hx : (cstar W).toReal < x)
    (hstay : (cstar W).toReal < x + z) :
    vcstar W (x + z) - vcstar W x -
      z * deriv (vcstar W) x = 0 := by
  rw [vcstar_eq_linear_gt_cstar W (x + z) hstay,
    vcstar_eq_linear_gt_cstar W x hx,
    vcstar_deriv_eq_one_above_cstar W x hx]
  ring
