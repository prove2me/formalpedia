-- Prove2me | solution 1 for CohnElkies.criticalBinaryExponent_lt_d33
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/8a0b92ae-6d88-4ce9-9a6d-b09f30f91083

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_criticalBinaryExponent_eq_three_halves_sub_logFourDivPi
import Theorems.Thm_CohnElkies_baseTwo_log_two_lt_d36
import Theorems.Thm_CohnElkies_baseTwo_log_four_div_pi_gt_d36

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
      (0.604400544291677695341677307053058 : ℝ) := by
  rw [criticalBinaryExponent_eq_three_halves_sub_logFourDivPi]
  have hden : 0 < 2 * Real.log (2 : ℝ) := by positivity
  have hratio :
      (3 / 2 : ℝ) - 0.604400544291677695341677307053058 <
        (Real.log (4 / Real.pi) + 1) / (2 * Real.log 2) := by
    apply (lt_div_iff₀ hden).2
    nlinarith [baseTwo_log_two_lt_d36,
      baseTwo_log_four_div_pi_gt_d36]
  linarith
end CohnElkies
