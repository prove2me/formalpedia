-- Prove2me | solution 1 for Comp.ModelData.coe_afInnerOf_outer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:35:20.707801+00:00
-- url     : https://prove2.me/submissions/a642dd02-c242-4c9a-943b-72fe3771f2ff

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_coe_afInnerOf
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    (↑(d.afInnerOf hs b y) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).AFOuter ↑b ↑y :=
  d.coe_afInnerOf hs h2 hnz b y
end Comp.ModelData
