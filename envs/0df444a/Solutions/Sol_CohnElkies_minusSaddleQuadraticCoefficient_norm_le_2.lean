-- Prove2me | solution 2 for CohnElkies.minusSaddleQuadraticCoefficient_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:55:43.91444+00:00
-- url     : https://prove2.me/submissions/a2e845b0-0bbb-47b4-8a11-5ca4bd0cec15

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution (z : ℂ) :
    ‖1 - 3 * Complex.I * z‖ ≤
      3 * (1 + ‖z‖) ^ 2 := by
  have h : ‖1 - 3 * Complex.I * z‖ ≤ 1 + 3 * ‖z‖ := by
    calc ‖1 - 3 * Complex.I * z‖ ≤ ‖(1:ℂ)‖ + ‖3 * Complex.I * z‖ := norm_sub_le _ _
      _ = 1 + 3 * ‖z‖ := by simp
  nlinarith [norm_nonneg z]

