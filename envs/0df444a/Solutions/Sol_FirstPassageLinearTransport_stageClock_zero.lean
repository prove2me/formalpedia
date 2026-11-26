-- Prove2me | solution 1 for FirstPassageLinearTransport.stageClock_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:09.168388+00:00
-- url     : https://prove2.me/submissions/063c537c-c72b-4917-91a2-54bd05fefd33

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
    stageClock p 0 n = 0 := rfl
end FirstPassageLinearTransport
