-- Prove2me | solution 1 for Comp.HideOrRun.hr_answers_AF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:35:06.304926+00:00
-- url     : https://prove2.me/submissions/e3884832-5795-4bac-9380-6a16233a9d36

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_hr_AF

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution :
    game.Answers game_wf (Objective.almostReach target) (Answer.region target) :=
  .almostReach hr_AF
end Comp.HideOrRun
