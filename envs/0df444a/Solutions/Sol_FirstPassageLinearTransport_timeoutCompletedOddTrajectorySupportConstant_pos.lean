-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutCompletedOddTrajectorySupportConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:09.087508+00:00
-- url     : https://prove2.me/submissions/079c3621-0de1-4b63-a971-a5c4c06f23f9

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_timeoutOddTrajectorySupportConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimeSupportConstant_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutCompletedOddTrajectorySupportConstant P C := by
  have htime := timeoutTimeSupportConstant_pos P C
  have hlog3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  unfold timeoutCompletedOddTrajectorySupportConstant
  exact add_pos (timeoutOddTrajectorySupportConstant_pos P C) htime
end FirstPassageLinearTransport
