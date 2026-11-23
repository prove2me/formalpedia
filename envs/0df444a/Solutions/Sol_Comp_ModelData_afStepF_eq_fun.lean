-- Prove2me | solution 1 for Comp.ModelData.afStepF_eq_fun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:27:30.804685+00:00
-- url     : https://prove2.me/submissions/c49615e4-066b-4a22-850d-4b660c7e40e0

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_afStepF_eq

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    d.toCsgQ.afStepF b y = d.afStepOf hs b y :=
  funext fun x => d.afStepF_eq hs hnn hnz b y x
end Comp.ModelData
