-- Prove2me | solution 2 for CohnElkies.criticalBinaryExponent_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/d29da356-ca02-45bf-9348-241c786706b8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_criticalPackingBase_pos
import Theorems.Thm_CohnElkies_logb_criticalPackingBase
import Theorems.Thm_CohnElkies_criticalPackingBase_lt_one

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
namespace CohnElkies
theorem _root_.solution : 0 < criticalBinaryExponent := by
  have hlog : Real.logb 2 criticalPackingBase < 0 := by
    exact (Real.logb_neg (by norm_num) criticalPackingBase_pos
      criticalPackingBase_lt_one)
  rw [logb_criticalPackingBase] at hlog
  linarith
end CohnElkies
