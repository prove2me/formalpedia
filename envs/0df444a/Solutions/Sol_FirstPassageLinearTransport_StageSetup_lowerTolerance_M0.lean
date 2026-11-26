-- Prove2me | solution 1 for FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:01.233819+00:00
-- url     : https://prove2.me/submissions/f50d1bc6-8e5f-4da5-b751-4e2e3653ee3c

import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace StageSetup
theorem _root_.solution
    {r eta : ℝ} (p : StageSetup r eta) (t : ℝ)
    (ht0 : 0 < t) (hteta : t ≤ eta) :
    (p.lowerTolerance t ht0 hteta).M0 = p.M0 := rfl
end StageSetup
end FirstPassageLinearTransport
