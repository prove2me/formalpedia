-- Prove2me | solution 1 for CohnElkies.criticalBinaryExponent_gt_d30
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/9489d94c-cc36-4c36-b9ac-ecb79bfaf575

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_criticalBinaryExponent_gt_d33

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open Finset
open CohnElkies
namespace CohnElkies
theorem _root_.solution :
    (0.604400544291677695341677307053 : ℝ) <
      criticalBinaryExponent := by
  nlinarith [criticalBinaryExponent_gt_d33]
end CohnElkies
