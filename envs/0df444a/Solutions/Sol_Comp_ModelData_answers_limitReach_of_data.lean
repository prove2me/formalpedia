-- Prove2me | solution 1 for Comp.ModelData.answers_limitReach_of_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:29:23.501799+00:00
-- url     : https://prove2.me/submissions/a0037854-71fb-42a1-b66b-5fdafed98246

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_mid_eq_of_data
import Theorems.Thm_Comp_CsgQ_LF_eq_coe_of_fixed
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (k : ℕ) (b y : Finset (Fin d.nStates)) (m : ℕ)
    (hlw : ∀ x s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅)
      = (d.lStepOf hs x y s)^[k] ∅)
    (hiter : (d.midOf hs k b y)^[m] ∅ = y) (hfix : d.midOf hs k b y y = y)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).LF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.limitReach b) (Answer.region y) :=
  .limitReach (CsgQ.LF_eq_coe_of_fixed d.toCsgQ (d.wellFormed hs h2) b y
    (d.mid_eq_of_data hs h2 hnz k b y y m hlw hiter hfix) hy)
end Comp.ModelData
