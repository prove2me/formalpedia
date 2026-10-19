-- Prove2me | solution 2 for CohnElkies.minusSaddleLinearCoefficient_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:04:17.792555+00:00
-- url     : https://prove2.me/submissions/da4a0b6f-d4f2-4e9e-88bd-602555beab9b

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
    ‖2 * z - Complex.I * (1 + 3 * z ^ 2)‖ ≤
      3 * (1 + ‖z‖) ^ 2 := by
  have hz := norm_nonneg z
  have h1 : ‖2 * z - Complex.I * (1 + 3 * z ^ 2)‖ ≤ 2 * ‖z‖ + (1 + 3 * ‖z‖ ^ 2) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    have : ‖(2:ℂ)‖ = 2 := by simp
    rw [this]
    refine add_le_add le_rfl ((norm_add_le _ _).trans ?_)
    rw [norm_one, norm_mul, norm_pow]
    have : ‖(3:ℂ)‖ = 3 := by simp
    rw [this]
  nlinarith

