-- Prove2me | solution 1 for Comp.HideOrRunData.hrd_answers_LF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:46:52.89816+00:00
-- url     : https://prove2.me/submissions/c704b44e-fc02-4811-9edc-c82936c85e5b

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
import Theorems.Thm_Comp_HideOrRunData_hrd_nonzero
import Theorems.Thm_Comp_ModelData_answers_limitReach_of_fix


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData
namespace Comp.HideOrRunData
theorem _root_.solution :
    hrd.toCsgQ.Answers hrd_wf (Objective.limitReach hrdTarget) (Answer.region hrdWinning) :=
  hrd.answers_limitReach_of_fix hrd_shape hrd_stochastic hrd_nonzero hrdTarget hrdWinning
    (by decide)
end Comp.HideOrRunData
