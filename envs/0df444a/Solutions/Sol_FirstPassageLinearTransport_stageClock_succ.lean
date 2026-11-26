-- Prove2me | solution 1 for FirstPassageLinearTransport.stageClock_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:50.405818+00:00
-- url     : https://prove2.me/submissions/95ce6231-d113-4438-b46c-9e6bef788646

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
    stageClock p (R + 1) n =
      stageLength p n + stageClock p R (stageMap p n) := rfl
end FirstPassageLinearTransport
