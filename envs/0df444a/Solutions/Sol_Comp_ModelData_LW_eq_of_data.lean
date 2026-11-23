-- Prove2me | solution 1 for Comp.ModelData.LW_eq_of_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:23:09.304461+00:00
-- url     : https://prove2.me/submissions/759c3ff4-5816-44d9-b58a-be77b92bbbe7

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_lStepF_eq
import Theorems.Thm_Comp_CsgQ_LW_eq_coe_of_fixed
import Theorems.Thm_Comp_ModelData_Stochastic_nonneg
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (hfix : d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅) = (d.lStepOf hs x y s)^[k] ∅) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LW ↑x ↑y s
      = (↑((d.lStepOf hs x y s)^[k] ∅) : Set (Fin d.nAct1)) :=
  CsgQ.LW_eq_coe_of_fixed d.toCsgQ (d.wellFormed hs h2) x y s _ k
    (by rw [d.lStepF_eq hs h2.nonneg hnz])
    (by rw [d.lStepF_eq hs h2.nonneg hnz]; exact hfix)
end Comp.ModelData
