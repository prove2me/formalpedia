-- Prove2me | solution 1 for CohnElkies.manuscriptPackingRoot_sub_deficit_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/dfffa072-38f7-487e-87b5-a8ed0faa615d

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
namespace CohnElkies
theorem _root_.solution (d : ℕ) :
    criticalPackingBase - manuscriptPackingDeficit d ≤
      (linearProgram d) ^ ((d : ℝ)⁻¹) := by
  have hdeficit :
      criticalPackingBase - (linearProgram d) ^ ((d : ℝ)⁻¹) ≤
        manuscriptPackingDeficit d := by
    exact le_max_right _ _
  linarith
end CohnElkies
