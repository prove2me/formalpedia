-- Prove2me | solution 1 for Comp.HideOrRun.coe_midStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:34:48.382747+00:00
-- url     : https://prove2.me/submissions/d38b387d-dd89-48a0-8eb8-0480554a51be

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_hr_LW
import Theorems.Thm_Comp_HideOrRun_lpre1F_eq_lpre1C
import Theorems.Thm_Comp_CsgQ_coe_LFInner_apply


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution (b y x : Finset HR) :
    (game.toCSG game_wf).LFInner ↑b ↑y ↑x = (↑(midStep b y x) : Set HR) := by
  rw [CsgQ.coe_LFInner_apply game game_wf b y x (fun s => lwC x y s) (fun s => hr_LW x y s),
    lpre1F_eq_lpre1C]
  rfl
end Comp.HideOrRun
