-- Prove2me | solution 1 for FirstPassageLinearTransport.rawOddDeviationCoefficient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:28:35.979151+00:00
-- url     : https://prove2.me/submissions/2bb2ba89-4c40-443e-a5bd-21044ec3662d

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    0 ≤ rawOddDeviationCoefficient := by
  unfold rawOddDeviationCoefficient
  exact mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) driftGap_pos.le) (by norm_num))
    (Real.log_pos (by norm_num)).le
end FirstPassageLinearTransport
