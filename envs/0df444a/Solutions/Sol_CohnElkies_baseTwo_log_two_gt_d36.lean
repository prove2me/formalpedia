-- Prove2me | solution 1 for CohnElkies.baseTwo_log_two_gt_d36
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/2b866fd5-dafd-4f32-b58d-4035dca2a3bf

import Mathlib
import Definitions.Def_SpherePacking

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
    (0.693147180559945309417232121458176568 : ℝ) < Real.log 2 := by
  have h := Real.sum_range_le_log_div
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 42
  norm_num [Finset.sum_range_succ] at h
  nlinarith
end CohnElkies
