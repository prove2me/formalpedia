-- Prove2me | solution 1 for Comp.ModelData.answers_sureSafe_of_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:27:41.525833+00:00
-- url     : https://prove2.me/submissions/bdb8216a-82e2-4174-b3cb-205348d52de9

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_gStepF_eq
import Theorems.Thm_Comp_ModelData_gStepF_eq_fun
import Theorems.Thm_Comp_CsgQ_answers_sureSafe
import Theorems.Thm_Comp_ModelData_Stochastic_nonneg
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (safe c : Finset (Fin d.nStates)) (n : ℕ)
    (hiter : (d.gStepOf hs safe)^[n] Finset.univ = c)
    (hfix : d.gStepOf hs safe c = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.sureSafe safe) (Answer.region c) := by
  refine CsgQ.answers_sureSafe d.toCsgQ (d.wellFormed hs h2) safe c n ?_ ?_
  · rw [d.gStepF_eq_fun hs h2.nonneg hnz safe]
    exact hiter
  · rw [d.gStepF_eq hs h2.nonneg hnz safe c]
    exact hfix
end Comp.ModelData
