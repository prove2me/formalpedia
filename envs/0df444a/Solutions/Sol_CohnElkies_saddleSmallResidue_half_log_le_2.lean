-- Prove2me | solution 2 for CohnElkies.saddleSmallResidue_half_log_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/9154d1c9-e01a-4576-a2f8-f3daa727c021

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
theorem _root_.solution :
    Real.log (1 / 2 : ℝ) ≤ -(1 / 2 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 1 / 2)
  linarith
end CohnElkies
