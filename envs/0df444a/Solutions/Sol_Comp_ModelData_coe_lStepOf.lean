-- Prove2me | solution 1 for Comp.ModelData.coe_lStepOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:24:31.175963+00:00
-- url     : https://prove2.me/submissions/147066ab-4c2d-42bb-ab9f-9614acc07e42

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_lStepF_eq
import Theorems.Thm_Comp_CsgQ_coe_lStepF
import Theorems.Thm_Comp_ModelData_Stochastic_nonneg
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (w : Finset (Fin d.nAct1)) :
    (↑(d.lStepOf hs x y s w) : Set (Fin d.nAct1))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).LStep ↑x ↑y s ↑w := by
  rw [← d.lStepF_eq hs h2.nonneg hnz x y s, CsgQ.coe_lStepF]
end Comp.ModelData
