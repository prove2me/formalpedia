-- Prove2me | solution 1 for Comp.ModelData.AF_eq_coe_afRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:40:48.171772+00:00
-- url     : https://prove2.me/submissions/6ba2e2e6-b21b-4ca0-878c-4b6a08c42851

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_coe_afInnerOf_outer
import Theorems.Thm_Comp_ModelData_wellFormed
import Theorems.Thm_Comp_gfp_eq_coe_fixFrom_univ


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b : Finset (Fin d.nStates)) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b
      = (↑(d.afRegion hs b) : Set (Fin d.nStates)) :=
  gfp_eq_coe_fixFrom_univ _ _ (d.coe_afInnerOf_outer hs h2 hnz b)
end Comp.ModelData
