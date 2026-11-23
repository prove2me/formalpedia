-- Prove2me | solution 1 for Comp.ModelData.afInner_eq_of_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:31:03.696791+00:00
-- url     : https://prove2.me/submissions/369d5af5-275b-46e9-b257-73477d8ae055

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_afStepF_eq
import Theorems.Thm_Comp_ModelData_afStepF_eq_fun
import Theorems.Thm_Comp_CsgQ_afInner_eq_coe_of_fixed
import Theorems.Thm_Comp_ModelData_Stochastic_nonneg
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y c : Finset (Fin d.nStates)) (m : ℕ)
    (hiter : (d.afStepOf hs b y)^[m] ∅ = c) (hfix : d.afStepOf hs b y c = c) :
    ((d.toCsgQ.toCSG (d.wellFormed hs h2)).AFInner ↑b ↑y).lfp =
      (↑c : Set (Fin d.nStates)) := by
  refine CsgQ.afInner_eq_coe_of_fixed d.toCsgQ (d.wellFormed hs h2) b y c m ?_ ?_
  · rw [d.afStepF_eq_fun hs h2.nonneg hnz b y]
    exact hiter
  · rw [d.afStepF_eq hs h2.nonneg hnz b y c]
    exact hfix
end Comp.ModelData
