-- Prove2me | solution 1 for Comp.ModelData.answers_almostReach_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:44:25.249808+00:00
-- url     : https://prove2.me/submissions/5247d131-8090-4ebc-ae8a-e1b4e513d0f4

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_AF_eq_coe_afRegion
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (b c : Finset (Fin d.nStates))
    (hc : d.afRegion hs b = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.almostReach b) (Answer.region c) := by
  subst hc
  exact .almostReach (d.AF_eq_coe_afRegion hs h2 hnz b)
end Comp.ModelData
