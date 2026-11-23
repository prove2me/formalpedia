-- Prove2me | solution 1 for Comp.ModelData.gStepF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:24:50.247041+00:00
-- url     : https://prove2.me/submissions/42676a32-ff4c-46ab-8ce5-f28b6ab3dbb3

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_pre1F_eq

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (safe x : Finset (Fin d.nStates)) :
    d.toCsgQ.gStepF safe x = d.gStepOf hs safe x := by
  unfold CsgQ.gStepF gStepOf
  rw [d.pre1F_eq hs hnn hnz x]
end Comp.ModelData
