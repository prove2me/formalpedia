-- Prove2me | solution 2 for CohnElkies.plusSaddleLinearCoefficient_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:58:07.892421+00:00
-- url     : https://prove2.me/submissions/ffe29a4c-6ba5-4d52-b36f-290a3766c4d3

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
    ‖2 * z + Complex.I * (1 + 3 * z ^ 2)‖ ≤
      3 * (1 + ‖z‖) ^ 2 := by
  have h : ‖2 * z + Complex.I * (1 + 3 * z ^ 2)‖ ≤ 2 * ‖z‖ + (1 + 3 * ‖z‖ ^ 2) := by
    calc ‖2 * z + Complex.I * (1 + 3 * z ^ 2)‖ ≤ ‖2 * z‖ + ‖Complex.I * (1 + 3 * z ^ 2)‖ := norm_add_le _ _
      _ ≤ 2 * ‖z‖ + (1 + 3 * ‖z‖ ^ 2) := by
        gcongr
        · simp
        · rw [norm_mul, Complex.norm_I, one_mul]
          calc ‖1 + 3 * z ^ 2‖ ≤ ‖(1:ℂ)‖ + ‖3 * z ^ 2‖ := norm_add_le _ _
            _ = 1 + 3 * ‖z‖ ^ 2 := by simp
  nlinarith [norm_nonneg z]

