-- Prove2me | solution 1 for Comp.ModelData.coe_afInnerOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:32:22.834604+00:00
-- url     : https://prove2.me/submissions/6d7aecbb-e885-4a87-85d6-219d7139af56

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_coe_afStepOf
import Theorems.Thm_Comp_ModelData_wellFormed
import Theorems.Thm_Comp_lfp_eq_coe_fixFrom_empty


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    (↑(d.afInnerOf hs b y) : Set (Fin d.nStates))
      = ((d.toCsgQ.toCSG (d.wellFormed hs h2)).AFInner ↑b ↑y).lfp :=
  (lfp_eq_coe_fixFrom_empty _ _ (d.coe_afStepOf hs h2 hnz b y)).symm
end Comp.ModelData
