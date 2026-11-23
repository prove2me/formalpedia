-- Prove2me | solution 1 for Comp.ModelData.afStepF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:59.666607+00:00
-- url     : https://prove2.me/submissions/fafdd54f-8df4-46fa-8d21-368c464ccdce

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_apre1F_eq

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (b y x : Finset (Fin d.nStates)) :
    d.toCsgQ.afStepF b y x = d.afStepOf hs b y x := by
  unfold CsgQ.afStepF afStepOf
  rw [d.apre1F_eq hs hnn hnz x y]
end Comp.ModelData
