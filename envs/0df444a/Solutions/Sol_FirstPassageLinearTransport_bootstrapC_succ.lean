-- Prove2me | solution 1 for FirstPassageLinearTransport.bootstrapC_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:22:03.235596+00:00
-- url     : https://prove2.me/submissions/2b186498-8f6b-45be-8253-6e599054e0c7

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
    (chi Dc : ℝ) (R : ℕ) :
    bootstrapC p chi Dc (R + 1) =
      pullbackGlobalConstant p chi Dc * (bootstrapC p chi Dc R + 1) *
        (bootstrapD chi Dc R)⁻¹ ^ 2 := rfl
end FirstPassageLinearTransport
