-- Prove2me | solution 2 for CohnElkies.criticalPackingBase_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/84dc427e-3e74-4f7c-b969-c21105d2ff26

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
namespace CohnElkies
theorem _root_.solution : criticalPackingBase < 1 := by
  unfold criticalPackingBase
  have hratio : Real.exp 1 / (2 * Real.pi) < 1 := by
    apply (div_lt_one (by positivity)).2
    nlinarith [Real.exp_one_lt_three, Real.pi_gt_three]
  exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
    (by simpa using! hratio)
end CohnElkies
