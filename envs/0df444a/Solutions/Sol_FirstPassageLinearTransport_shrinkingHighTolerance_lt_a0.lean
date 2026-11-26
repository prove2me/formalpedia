-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingHighTolerance_lt_a0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:17:12.033941+00:00
-- url     : https://prove2.me/submissions/9f80b97e-4b0f-45e1-8bf2-24580a7ef8e1

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) (M m : ℕ) :
    shrinkingHighTolerance P M m < a0 :=
  (shrinkingHighTolerance_le_tau P M m).trans_lt P.tau_lt_a0
end FirstPassageLinearTransport
