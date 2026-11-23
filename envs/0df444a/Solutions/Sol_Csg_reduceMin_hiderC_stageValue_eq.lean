-- Prove2me | solution 1 for Csg.reduceMin_hiderC_stageValue_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:05:33.584352+00:00
-- url     : https://prove2.me/submissions/a529b3ed-f13b-4fde-9dff-de1f45bcd08f

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition
import Theorems.Thm_Csg_reduceMin_hiderC_stageGame_eq
import Theorems.Thm_Csg_MatrixGame_value_relabelCol
import Theorems.Thm_Csg_MatrixGame_value_relabelRow
import Theorems.Thm_Csg_stageValue_min_eq


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : SkirmishState → ℝ) (vhide : v .hide = 4 / 5)
    (vhome : v .home = 1) (vwet : v .wet = 0) :
    (skirmishNCSG.reduceMin hiderC).stageValue .hide v = 4 / 5 := by
  unfold CSG.stageValue
  rw [reduceMin_hiderC_stageGame_eq, MatrixGame.value_relabelCol, MatrixGame.value_relabelRow]
  exact stageValue_min_eq v vhide vhome vwet
end Csg
