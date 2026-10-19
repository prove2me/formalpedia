-- Prove2me | solution 2 for CohnElkies.rpow_two_pow_inv_dimension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:55:29.137887+00:00
-- url     : https://prove2.me/submissions/905bcb3e-fd3d-4a21-b5a7-08e3cdb56bd7

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology


theorem solution {d : ℕ} (hd : 0 < d) :
    ((2 : ℝ) ^ d) ^ ((d : ℝ)⁻¹) = 2 := by
  exact Real.pow_rpow_inv_natCast (by norm_num) hd.ne'

