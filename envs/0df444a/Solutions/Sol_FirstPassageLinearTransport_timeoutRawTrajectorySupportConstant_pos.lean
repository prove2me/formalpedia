-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutRawTrajectorySupportConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:22.542183+00:00
-- url     : https://prove2.me/submissions/c7af7db1-3aaf-4a6a-ae7e-c03312849c39

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_rawOddDeviationCoefficient_nonneg
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimeSupportConstant_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutRawTrajectorySupportConstant P C := by
  have htime := timeoutTimeSupportConstant_pos P C
  have hcoef := rawOddDeviationCoefficient_nonneg
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold timeoutRawTrajectorySupportConstant
  positivity
end FirstPassageLinearTransport
