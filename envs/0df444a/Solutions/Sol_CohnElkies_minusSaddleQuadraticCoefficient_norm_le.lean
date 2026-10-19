-- Prove2me | solution 1 for CohnElkies.minusSaddleQuadraticCoefficient_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/2307e1a0-7d4b-4d42-8cd6-766f994aec96

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
    ‖1 - 3 * Complex.I * z‖ ≤
      3 * (1 + ‖z‖) ^ 2 := by
  calc
    ‖1 - 3 * Complex.I * z‖ ≤
        ‖(1 : ℂ)‖ + ‖(3 : ℂ) * Complex.I * z‖ :=
      norm_sub_le _ _
    _ = 1 + 3 * ‖z‖ := by
      simp
    _ ≤ 3 * (1 + ‖z‖) ^ 2 := by
      nlinarith [norm_nonneg z, sq_nonneg ‖z‖]
end CohnElkies
