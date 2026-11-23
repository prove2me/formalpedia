-- Prove2me | solution 1 for Comp.ModelData.answers_limitReach_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:44:40.648801+00:00
-- url     : https://prove2.me/submissions/5dab39e0-02f6-4f66-b566-3647344f3075

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_LF_eq_coe_lfRegion
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (b c : Finset (Fin d.nStates))
    (hc : d.lfRegion hs b = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.limitReach b) (Answer.region c) := by
  subst hc
  exact .limitReach (d.LF_eq_coe_lfRegion hs h2 hnz b)
end Comp.ModelData
