-- Prove2me | solution 1 for FirstPassageLinearTransport.stageK_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:10.361233+00:00
-- url     : https://prove2.me/submissions/d78c869e-aef8-4e27-b5de-94f745b4f4c3

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
    1 ≤ stageK p := by
  unfold stageK
  exact one_le_pow₀ (by norm_num)
end FirstPassageLinearTransport
