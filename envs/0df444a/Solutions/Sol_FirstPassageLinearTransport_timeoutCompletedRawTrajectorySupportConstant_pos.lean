-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutCompletedRawTrajectorySupportConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:07.028784+00:00
-- url     : https://prove2.me/submissions/424254f4-5bb4-41b2-9fa2-476f7ec7bff0

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_rawOddDeviationCoefficient_nonneg
import Theorems.Thm_FirstPassageLinearTransport_timeoutCompletedOddTrajectorySupportConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimeSupportConstant_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutCompletedRawTrajectorySupportConstant P C := by
  have htime := timeoutTimeSupportConstant_pos P C
  have hcoef := rawOddDeviationCoefficient_nonneg
  have hodd := timeoutCompletedOddTrajectorySupportConstant_pos P C
  unfold timeoutCompletedRawTrajectorySupportConstant
  positivity
end FirstPassageLinearTransport
