-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutHighTolerance_lt_a0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:57.904934+00:00
-- url     : https://prove2.me/submissions/c38d1e74-5d1f-47a7-9ec2-3233e654ee46

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) (M m : ℕ) :
    timeoutHighTolerance P M m < a0 :=
  (timeoutHighTolerance_le_tau P M m).trans_lt P.tau_lt_a0
end FirstPassageLinearTransport
