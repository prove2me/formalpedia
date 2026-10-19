-- Prove2me | solution 2 for CohnElkies.saddleSourcePositiveShellThirdMoment_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:18:17.086527+00:00
-- url     : https://prove2.me/submissions/801019cd-1801-4baa-aaf2-c92e46fc56fa

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    {ε : ℝ} (hε : 0 < ε) (δ : ℝ) :
    0 ≤ upperPositiveShellThirdMoment ε δ := by
  unfold upperPositiveShellThirdMoment
  have hloc : 0 ≤ shellLocation ε := by unfold shellLocation; positivity
  apply intervalIntegral.integral_nonneg (by linarith)
  intro a ha
  have ha0 : 0 ≤ a := le_trans hloc ha.1
  unfold positiveShellDensity shellWeight
  exact mul_nonneg (mul_nonneg (div_nonneg (Real.exp_pos _).le (Real.cosh_pos a).le) (pow_nonneg ha0 3)) (Real.cosh_pos _).le

