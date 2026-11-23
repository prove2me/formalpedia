-- Prove2me | solution 1 for Comp.HideOrRun.hr_LW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:48:46.750531+00:00
-- url     : https://prove2.me/submissions/192b238a-af3a-4cda-91e4-ebffeaaf6960

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_lStepF_eq
import Theorems.Thm_Comp_HideOrRun_lw_fixed
import Theorems.Thm_Comp_CsgQ_LW_eq_coe_of_fixed


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution (x y : Finset HR) (s : HR) :
    (game.toCSG game_wf).LW ↑x ↑y s = (↑(lwC x y s) : Set Bool) :=
  CsgQ.LW_eq_coe_of_fixed game game_wf x y s (lwC x y s) 2 (by rw [lStepF_eq]; rfl)
    (by rw [lStepF_eq]; exact lw_fixed x y s)
end Comp.HideOrRun
