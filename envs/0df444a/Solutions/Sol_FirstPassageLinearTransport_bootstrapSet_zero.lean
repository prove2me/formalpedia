-- Prove2me | solution 1 for FirstPassageLinearTransport.bootstrapSet_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:12:52.187801+00:00
-- url     : https://prove2.me/submissions/4aaecad7-1162-4048-8c98-c66123607f53

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta) :
    bootstrapSet p 0 = extendedWindow p := rfl
end FirstPassageLinearTransport
