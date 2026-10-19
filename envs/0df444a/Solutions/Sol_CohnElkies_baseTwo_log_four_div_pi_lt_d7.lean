-- Prove2me | solution 1 for CohnElkies.baseTwo_log_four_div_pi_lt_d7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/19dc5a0e-44df-48ac-9212-46ebe1971792

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
    Real.log (4 / Real.pi) < (0.2415647 : ℝ) := by
  have hp : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have harg : (4 : ℝ) / Real.pi < 4 / 3.141592 := by
    apply (div_lt_div_iff₀ Real.pi_pos
      (by norm_num : (0 : ℝ) < 3.141592)).2
    nlinarith
  have hmono := Real.log_lt_log
    (by positivity : (0 : ℝ) < 4 / Real.pi) harg
  have hs := Real.log_div_le_sum_range_add
    (x := (107301 / 892699 : ℝ)) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hs
  norm_num at hmono
  nlinarith
end CohnElkies
