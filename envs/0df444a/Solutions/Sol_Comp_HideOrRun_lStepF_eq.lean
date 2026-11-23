-- Prove2me | solution 1 for Comp.HideOrRun.lStepF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:47:37.353892+00:00
-- url     : https://prove2.me/submissions/08e1c30b-1983-4870-8346-7b9c647f24d4

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_aF_eq_aC
import Theorems.Thm_Comp_HideOrRun_bF_eq_bC

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution (x y : Finset HR) (s : HR) : game.lStepF x y s = lStepC x y s := by
  funext w
  unfold CsgQ.lStepF lStepC
  rw [bF_eq_bC, aF_eq_aC]
end Comp.HideOrRun
