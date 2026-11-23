-- Prove2me | solution 1 for Comp.HideOrRunData.hrd_answers_LF_counted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:37:55.888821+00:00
-- url     : https://prove2.me/submissions/906a8f6c-85cd-4bd7-a03a-287fb4ea32eb

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
import Theorems.Thm_Comp_HideOrRunData_hrd_nonzero
import Theorems.Thm_Comp_HideOrRunData_hrd_lw
import Theorems.Thm_Comp_HideOrRunData_hrd_LF_le
import Theorems.Thm_Comp_ModelData_answers_limitReach_of_data


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData
set_option maxRecDepth 4000
namespace Comp.HideOrRunData
theorem _root_.solution :
    hrd.toCsgQ.Answers hrd_wf (Objective.limitReach hrdTarget) (Answer.region hrdWinning) :=
  hrd.answers_limitReach_of_data hrd_shape hrd_stochastic hrd_nonzero 2 hrdTarget hrdWinning 2
    (fun x s => hrd_lw x hrdWinning s) (by decide) (by decide) hrd_LF_le
end Comp.HideOrRunData
