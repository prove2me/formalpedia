-- Prove2me | solution 2 for CohnElkies.saddleSourcePositiveShellVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:46.077424+00:00
-- url     : https://prove2.me/submissions/6ad3c61a-9a48-47b1-a82c-beb3d0307d3e

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology


theorem solution
    (ε δ : ℝ) :
    0 ≤ upperPositiveShellVariance ε δ := by
  unfold upperPositiveShellVariance
  apply intervalIntegral.integral_nonneg (by linarith)
  intro a _
  unfold positiveShellDensity shellWeight
  have := Real.cosh_pos a
  have := Real.cosh_pos ((1 + δ) * a)
  positivity

