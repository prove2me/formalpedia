-- Prove2me | solution 1 for FirstPassageLinearTransport.stageOrbit_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:12:53.484226+00:00
-- url     : https://prove2.me/submissions/6ccac22c-5616-41e8-98dd-d218b896bf35

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta) (n : ℕ) :
    stageOrbit p 0 n = n := rfl
end FirstPassageLinearTransport
