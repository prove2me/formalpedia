-- Prove2me | solution 2 for CohnElkies.manuscriptPackingRoot_sub_deficit_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:14:09.770534+00:00
-- url     : https://prove2.me/submissions/c72eac1f-0440-49ac-8fe7-2ed451cb097b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology


theorem solution (d : ℕ) :
    criticalPackingBase - manuscriptPackingDeficit d ≤
      (linearProgram d) ^ ((d : ℝ)⁻¹) := by
  unfold manuscriptPackingDeficit
  linarith [le_max_right 0 (criticalPackingBase - (linearProgram d) ^ ((d : ℝ)⁻¹))]

