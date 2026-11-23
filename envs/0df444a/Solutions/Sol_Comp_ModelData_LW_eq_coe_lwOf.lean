-- Prove2me | solution 1 for Comp.ModelData.LW_eq_coe_lwOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:51.368298+00:00
-- url     : https://prove2.me/submissions/838d6c64-5531-4734-801e-e4b4f678630a

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_coe_lStepOf
import Theorems.Thm_Comp_ModelData_wellFormed
import Theorems.Thm_Comp_lfp_eq_coe_fixFrom_empty


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LW ↑x ↑y s
      = (↑(d.lwOf hs x y s) : Set (Fin d.nAct1)) :=
  lfp_eq_coe_fixFrom_empty _ _ (d.coe_lStepOf hs h2 hnz x y s)
end Comp.ModelData
