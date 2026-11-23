-- Prove2me | solution 1 for Csg.reduceMax_hiderC_stageValue_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:05:22.656366+00:00
-- url     : https://prove2.me/submissions/774b9f52-c67e-4947-a87a-6825f53d0e02

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition
import Theorems.Thm_Csg_reduceMax_hiderC_stageGame_eq
import Theorems.Thm_Csg_MatrixGame_value_relabelCol
import Theorems.Thm_Csg_MatrixGame_value_relabelRow
import Theorems.Thm_Csg_stageValue_max_eq


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : SkirmishState → ℝ) (vhide : v .hide = 1 / 2)
    (vhome : v .home = 1) (vwet : v .wet = 0) :
    (skirmishNCSG.reduceMax hiderC).stageValue .hide v = 1 / 2 := by
  unfold CSG.stageValue
  rw [reduceMax_hiderC_stageGame_eq, MatrixGame.value_relabelCol, MatrixGame.value_relabelRow]
  exact stageValue_max_eq v vhide vhome vwet
end Csg
