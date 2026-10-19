-- Prove2me | solution 1 for CohnElkies.criticalBinaryExponent_lt_d30
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/c00d34f7-4b5c-4a5f-b588-a38bf1437c04

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_criticalBinaryExponent_lt_d33

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
    criticalBinaryExponent <
      (0.604400544291677695341677307054 : ℝ) := by
  nlinarith [criticalBinaryExponent_lt_d33]
end CohnElkies
