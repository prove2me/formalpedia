-- Prove2me | solution 1 for FirstPassageLinearTransport.bootstrapSet_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:12:57.5404+00:00
-- url     : https://prove2.me/submissions/b058253e-38b2-490a-902d-1a5c9e68cb88

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta) (R : ℕ) :
    bootstrapSet p (R + 1) = firstPassagePullback p (bootstrapSet p R) := rfl
end FirstPassageLinearTransport
