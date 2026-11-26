-- Prove2me | solution 1 for FirstPassageLinearTransport.stageMap_is_actual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:55.044134+00:00
-- url     : https://prove2.me/submissions/dc03f8c2-ee87-4ca8-8c95-977ec9117349

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta) (n : ℕ) :
    stageMap p n = orbit (stageLength p n) n := rfl
end FirstPassageLinearTransport
