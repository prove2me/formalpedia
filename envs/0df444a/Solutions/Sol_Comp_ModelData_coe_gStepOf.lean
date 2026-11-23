-- Prove2me | solution 1 for Comp.ModelData.coe_gStepOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:26:11.233222+00:00
-- url     : https://prove2.me/submissions/abfb8efb-9592-4273-b274-cd4756285d50

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_gStepF_eq
import Theorems.Thm_Comp_CsgQ_GOrderHom_toCSG
import Theorems.Thm_Comp_CsgQ_coe_gStepF
import Theorems.Thm_Comp_ModelData_Stochastic_nonneg
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (safe x : Finset (Fin d.nStates)) :
    (↑(d.gStepOf hs safe x) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).GOrderHom ↑safe ↑x := by
  rw [← d.gStepF_eq hs h2.nonneg hnz safe x, CsgQ.coe_gStepF, CsgQ.GOrderHom_toCSG]
end Comp.ModelData
