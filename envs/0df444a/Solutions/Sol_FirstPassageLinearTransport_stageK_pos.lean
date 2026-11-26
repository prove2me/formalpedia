-- Prove2me | solution 1 for FirstPassageLinearTransport.stageK_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:11.614688+00:00
-- url     : https://prove2.me/submissions/7c8224ea-3141-4e97-a0ee-5172c3838ced

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
    0 < stageK p := by unfold stageK; positivity
end FirstPassageLinearTransport
