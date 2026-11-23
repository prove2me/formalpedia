-- Prove2me | solution 1 for Comp.ModelData.coe_lmidOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:28:33.359191+00:00
-- url     : https://prove2.me/submissions/9d75f932-1230-40d4-896a-23f0fbc2d7b6

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_lpre1F_eq
import Theorems.Thm_Comp_ModelData_LW_eq_coe_lwOf
import Theorems.Thm_Comp_CsgQ_coe_LFInner_apply
import Theorems.Thm_Comp_ModelData_Stochastic_nonneg
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y x : Finset (Fin d.nStates)) :
    (↑(d.lmidOf hs b y x) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y ↑x := by
  unfold lmidOf
  rw [CsgQ.coe_LFInner_apply d.toCsgQ (d.wellFormed hs h2) b y x (d.lwOf hs x y)
      (fun s => d.LW_eq_coe_lwOf hs h2 hnz x y s), d.lpre1F_eq hs h2.nonneg hnz]
end Comp.ModelData
