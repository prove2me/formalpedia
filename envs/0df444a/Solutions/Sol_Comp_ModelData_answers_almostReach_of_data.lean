-- Prove2me | solution 1 for Comp.ModelData.answers_almostReach_of_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:29:28.924807+00:00
-- url     : https://prove2.me/submissions/613f4942-5b84-4d7b-b581-10b412fdc3fd

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_afInner_eq_of_data
import Theorems.Thm_Comp_CsgQ_AF_eq_coe_of_fixed
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) (m : ℕ)
    (hiter : (d.afStepOf hs b y)^[m] ∅ = y) (hfix : d.afStepOf hs b y y = y)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.almostReach b) (Answer.region y) :=
  .almostReach (CsgQ.AF_eq_coe_of_fixed d.toCsgQ (d.wellFormed hs h2) b y
    (d.afInner_eq_of_data hs h2 hnz b y y m hiter hfix) hy)
end Comp.ModelData
