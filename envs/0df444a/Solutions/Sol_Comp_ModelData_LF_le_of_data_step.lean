-- Prove2me | solution 1 for Comp.ModelData.LF_le_of_data_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:32:55.268483+00:00
-- url     : https://prove2.me/submissions/574ff8ba-39b0-4210-9ff3-8adde94fd97b

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_mid_eq_of_data
import Theorems.Thm_Comp_CsgQ_LF_le_of_step
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (b y c : Finset (Fin d.nStates)) (m : ℕ)
    (hlw : ∀ x s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅)
      = (d.lStepOf hs x y s)^[k] ∅)
    (hiter : (d.midOf hs k b y)^[m] ∅ = c) (hfix : d.midOf hs k b y c = c)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).LF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LF ↑b ≤ (↑c : Set (Fin d.nStates)) :=
  CsgQ.LF_le_of_step d.toCsgQ (d.wellFormed hs h2) b y c
    (d.mid_eq_of_data hs h2 hnz k b y c m hlw hiter hfix) hy
end Comp.ModelData
