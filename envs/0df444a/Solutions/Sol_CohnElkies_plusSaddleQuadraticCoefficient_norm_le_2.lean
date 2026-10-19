-- Prove2me | solution 2 for CohnElkies.plusSaddleQuadraticCoefficient_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:08:10.13644+00:00
-- url     : https://prove2.me/submissions/d053d5d4-9d14-4362-9c10-874c818d973e

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
    ‖1 + 3 * Complex.I * z‖ ≤
      3 * (1 + ‖z‖) ^ 2 := by
  calc ‖1 + 3 * Complex.I * z‖ ≤ ‖(1:ℂ)‖ + ‖3 * Complex.I * z‖ := norm_add_le _ _
    _ = 1 + 3 * ‖z‖ := by simp
    _ ≤ 3 * (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]

