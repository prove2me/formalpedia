-- Prove2me | solution 1 for Comp.ModelData.gStepF_eq_fun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:26:00.1248+00:00
-- url     : https://prove2.me/submissions/a4ce59e4-5ad8-4a74-85f9-39dc463bb96e

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_gStepF_eq

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (safe : Finset (Fin d.nStates)) :
    d.toCsgQ.gStepF safe = d.gStepOf hs safe :=
  funext fun x => d.gStepF_eq hs hnn hnz safe x
end Comp.ModelData
