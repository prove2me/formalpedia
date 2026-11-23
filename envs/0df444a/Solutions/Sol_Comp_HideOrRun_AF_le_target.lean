-- Prove2me | solution 1 for Comp.HideOrRun.AF_le_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:52:38.139196+00:00
-- url     : https://prove2.me/submissions/26aa9d3e-1535-4686-bd69-b667bdd4927d

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_AF_le_winning
import Theorems.Thm_Comp_HideOrRun_afInner_at_winning
import Theorems.Thm_Comp_CsgQ_AF_le_of_step


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution : (game.toCSG game_wf).AF ↑target ≤ (↑target : Set HR) :=
  CsgQ.AF_le_of_step game game_wf target winning target afInner_at_winning AF_le_winning
end Comp.HideOrRun
