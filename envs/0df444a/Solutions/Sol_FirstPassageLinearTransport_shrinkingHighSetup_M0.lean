-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingHighSetup_M0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:11:40.021171+00:00
-- url     : https://prove2.me/submissions/545585d0-2188-4d50-9cbd-5292a5ec7da0

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
    (shrinkingHighSetup P M m).M0 = P.pHi.M0 := rfl
end FirstPassageLinearTransport
