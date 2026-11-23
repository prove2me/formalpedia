-- Prove2me | solution 1 for Comp.ModelData.coe_lfInnerOf_outer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:35:43.016808+00:00
-- url     : https://prove2.me/submissions/0463d778-8828-4857-96dd-ec338a586377

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_coe_lfInnerOf
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    (↑(d.lfInnerOf hs b y) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).LFOuter ↑b ↑y :=
  d.coe_lfInnerOf hs h2 hnz b y
end Comp.ModelData
