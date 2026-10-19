-- Prove2me | solution 1 for CohnElkies.baseTwo_log_two_lt_d36
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/ff29eb31-ae9e-48df-8ea4-f60ca51ebdd1

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
    Real.log 2 <
      (0.693147180559945309417232121458176569 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 42
  norm_num [Finset.sum_range_succ] at h
  nlinarith
end CohnElkies
