-- Prove2me | solution 1 for CohnElkies.criticalBinaryExponent_mem_Ioo_d30
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/66f309e3-e4d8-4c3e-9525-8e83d785921b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_criticalBinaryExponent_gt_d30
import Theorems.Thm_CohnElkies_criticalBinaryExponent_lt_d30

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
    criticalBinaryExponent ∈ Set.Ioo
      (0.604400544291677695341677307053 : ℝ)
      0.604400544291677695341677307054 :=
  ⟨criticalBinaryExponent_gt_d30, criticalBinaryExponent_lt_d30⟩
end CohnElkies
