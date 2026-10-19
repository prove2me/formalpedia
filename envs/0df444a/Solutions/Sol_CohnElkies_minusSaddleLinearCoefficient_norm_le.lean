-- Prove2me | solution 1 for CohnElkies.minusSaddleLinearCoefficient_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/aa3fd61f-ecc7-417a-911c-6837be7bc4ca

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
namespace CohnElkies
theorem _root_.solution (z : ℂ) :
    ‖2 * z - Complex.I * (1 + 3 * z ^ 2)‖ ≤
      3 * (1 + ‖z‖) ^ 2 := by
  have hinner :
      ‖(1 : ℂ) + 3 * z ^ 2‖ ≤ 1 + 3 * ‖z‖ ^ 2 := by
    calc
      ‖(1 : ℂ) + 3 * z ^ 2‖ ≤
          ‖(1 : ℂ)‖ + ‖(3 : ℂ) * z ^ 2‖ :=
        norm_add_le _ _
      _ = 1 + 3 * ‖z‖ ^ 2 := by
        simp [norm_pow]
  calc
    ‖2 * z - Complex.I * (1 + 3 * z ^ 2)‖ ≤
        ‖(2 : ℂ) * z‖ +
          ‖Complex.I * (1 + 3 * z ^ 2)‖ :=
      norm_sub_le _ _
    _ = 2 * ‖z‖ + ‖(1 : ℂ) + 3 * z ^ 2‖ := by
      simp
    _ ≤ 2 * ‖z‖ + (1 + 3 * ‖z‖ ^ 2) := by
      gcongr
    _ ≤ 3 * (1 + ‖z‖) ^ 2 := by
      nlinarith [norm_nonneg z]
end CohnElkies
