-- Prove2me | solution 1 for Comp.mp_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:32:31.274945+00:00
-- url     : https://prove2.me/submissions/559aab8a-f3be-4a36-8918-8af1d5d034db

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Comp_RockPaperScissorsQ
import Theorems.Thm_Comp_mp_valueCert
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
theorem _root_.solution : mpMatrixQ.toMatrixGame.value = 0 := by
  simpa using MatrixGameQ.value_eq_of_valueCert mp_valueCert
end Comp
