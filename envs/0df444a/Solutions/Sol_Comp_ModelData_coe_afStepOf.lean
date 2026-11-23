-- Prove2me | solution 1 for Comp.ModelData.coe_afStepOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:27:54.453807+00:00
-- url     : https://prove2.me/submissions/2d7b66e5-61df-471b-82cc-dd34f33bcebc

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_afStepF_eq
import Theorems.Thm_Comp_CsgQ_coe_AFInner_apply
import Theorems.Thm_Comp_ModelData_Stochastic_nonneg
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y x : Finset (Fin d.nStates)) :
    (↑(d.afStepOf hs b y x) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).AFInner ↑b ↑y ↑x := by
  rw [← d.afStepF_eq hs h2.nonneg hnz b y x, CsgQ.coe_AFInner_apply]
end Comp.ModelData
