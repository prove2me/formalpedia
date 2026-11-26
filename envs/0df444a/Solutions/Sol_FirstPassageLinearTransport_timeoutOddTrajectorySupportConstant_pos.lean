-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutOddTrajectorySupportConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:25:13.598918+00:00
-- url     : https://prove2.me/submissions/b0e40d62-24e0-4ccd-98c7-2cf2de2f082a

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimeSupportConstant_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutOddTrajectorySupportConstant P C := by
  have htime := timeoutTimeSupportConstant_pos P C
  have hlog3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  unfold timeoutOddTrajectorySupportConstant
  positivity
end FirstPassageLinearTransport
