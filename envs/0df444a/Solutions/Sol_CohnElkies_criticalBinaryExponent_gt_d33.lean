-- Prove2me | solution 1 for CohnElkies.criticalBinaryExponent_gt_d33
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/d7c962f4-7ed7-43c1-abf8-0c3716a0b5a0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_criticalBinaryExponent_eq_three_halves_sub_logFourDivPi
import Theorems.Thm_CohnElkies_baseTwo_log_two_gt_d36
import Theorems.Thm_CohnElkies_baseTwo_log_four_div_pi_lt_d36

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
    (0.604400544291677695341677307053057 : ℝ) <
      criticalBinaryExponent := by
  rw [criticalBinaryExponent_eq_three_halves_sub_logFourDivPi]
  have hden : 0 < 2 * Real.log (2 : ℝ) := by positivity
  have hratio :
      (Real.log (4 / Real.pi) + 1) / (2 * Real.log 2) <
        (3 / 2 : ℝ) -
          0.604400544291677695341677307053057 := by
    apply (div_lt_iff₀ hden).2
    nlinarith [baseTwo_log_two_gt_d36,
      baseTwo_log_four_div_pi_lt_d36]
  linarith
end CohnElkies
