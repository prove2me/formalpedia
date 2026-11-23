-- Prove2me | solution 1 for Comp.rps_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:32:26.043124+00:00
-- url     : https://prove2.me/submissions/69d8ebc6-bac8-4fb1-80f6-2bf8e6abc868

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Comp_RockPaperScissorsQ
import Theorems.Thm_Comp_rps_valueCert
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
import Theorems.Thm_Comp_MatrixGameQ_value_eq_of_valueCert
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution : rpsMatrixQ.toMatrixGame.value = 0 := by
  simpa using MatrixGameQ.value_eq_of_valueCert rps_valueCert
end Comp
