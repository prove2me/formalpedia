-- Prove2me | solution 1 for FirstPassageLinearTransport.stageOrbit_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:34:40.968745+00:00
-- url     : https://prove2.me/submissions/5a21aa89-9fdc-4f8d-a922-19a225a2885e

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta) (R n : ℕ) :
    stageOrbit p (R + 1) n = stageOrbit p R (stageMap p n) := rfl
end FirstPassageLinearTransport
