-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutOddTrajectorySupportConstant_le_completed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:49:51.693309+00:00
-- url     : https://prove2.me/submissions/3f96a6ba-da7a-49f6-beeb-f77b4144f66f

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
    timeoutOddTrajectorySupportConstant P C ≤
      timeoutCompletedOddTrajectorySupportConstant P C := by
  rw [timeoutCompletedOddTrajectorySupportConstant]
  linarith [timeoutTimeSupportConstant_pos P C]
end FirstPassageLinearTransport
