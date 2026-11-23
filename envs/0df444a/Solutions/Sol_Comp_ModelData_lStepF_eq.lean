-- Prove2me | solution 1 for Comp.ModelData.lStepF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:21:57.952272+00:00
-- url     : https://prove2.me/submissions/b6cfc8d7-284a-4ae4-9d06-fb2ed7296638

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_aF_eq
import Theorems.Thm_Comp_ModelData_bF_eq

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    d.toCsgQ.lStepF x y s = d.lStepOf hs x y s := by
  funext w
  unfold CsgQ.lStepF lStepOf
  rw [d.bF_eq hs hnn hnz, d.aF_eq hs hnn hnz]
end Comp.ModelData
