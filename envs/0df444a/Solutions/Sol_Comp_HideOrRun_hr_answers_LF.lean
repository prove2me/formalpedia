-- Prove2me | solution 1 for Comp.HideOrRun.hr_answers_LF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:35:05.815559+00:00
-- url     : https://prove2.me/submissions/0d5baece-f572-4d16-b585-5a8586e46622

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
import Theorems.Thm_Comp_HideOrRun_hr_LF

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun
namespace Comp.HideOrRun
theorem _root_.solution :
    game.Answers game_wf (Objective.limitReach target) (Answer.region winning) :=
  .limitReach hr_LF
end Comp.HideOrRun
