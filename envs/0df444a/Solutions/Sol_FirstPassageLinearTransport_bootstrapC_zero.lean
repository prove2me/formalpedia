-- Prove2me | solution 1 for FirstPassageLinearTransport.bootstrapC_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:07.371546+00:00
-- url     : https://prove2.me/submissions/0570bd58-71c8-4ab6-8147-b08c6b47ee19

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta)
    (chi Dc : ℝ) :
    bootstrapC p chi Dc 0 = quadraticWindowGlobalConstant eta := rfl
end FirstPassageLinearTransport
