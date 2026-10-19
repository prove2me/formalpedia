-- Prove2me | solution 2 for CohnElkies.saddleSourceFirstBranchVarianceCoefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:16.745804+00:00
-- url     : https://prove2.me/submissions/d3708ccc-0262-4aef-9c15-e549ed498e12

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology


theorem solution
    {ε : ℝ} (hε : 0 < ε) :
    0 < saddleSourceFirstBranchVarianceCoefficient ε := by
  unfold saddleSourceFirstBranchVarianceCoefficient
  have hV : 0 ≤ upperPositiveShellVariance ε (ε / 2) := by
    unfold upperPositiveShellVariance
    apply intervalIntegral.integral_nonneg (by linarith)
    intro a _
    unfold positiveShellDensity
    exact mul_nonneg (mul_nonneg (div_pos (by unfold shellWeight; exact Real.exp_pos _)
      (Real.cosh_pos _)).le (sq_nonneg a)) (Real.cosh_pos _).le
  have : 0 ≤ (2 + ε / 2) * upperPositiveShellVariance ε (ε / 2) := mul_nonneg (by linarith) hV
  linarith

