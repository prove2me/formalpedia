-- Prove2me | solution 1 for Comp.ModelData.answers_sureSafe_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:32:25.42982+00:00
-- url     : https://prove2.me/submissions/b6cb561c-1d9d-4e12-af8c-83466478c46a

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_G_eq_coe_gRegion
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (safe c : Finset (Fin d.nStates))
    (hc : d.gRegion hs safe = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.sureSafe safe) (Answer.region c) := by
  subst hc
  exact .sureSafe (d.G_eq_coe_gRegion hs h2 hnz safe)
end Comp.ModelData
