-- Prove2me | solution 1 for Comp.HideOrRunData.hrd_answers_AF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:46:53.454817+00:00
-- url     : https://prove2.me/submissions/c9c84730-6457-43d6-964c-05ca885ff43c

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
import Theorems.Thm_Comp_HideOrRunData_hrd_nonzero
import Theorems.Thm_Comp_ModelData_answers_almostReach_of_fix


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData
namespace Comp.HideOrRunData
theorem _root_.solution :
    hrd.toCsgQ.Answers hrd_wf (Objective.almostReach hrdTarget) (Answer.region hrdTarget) :=
  hrd.answers_almostReach_of_fix hrd_shape hrd_stochastic hrd_nonzero hrdTarget hrdTarget
    (by decide)
end Comp.HideOrRunData
