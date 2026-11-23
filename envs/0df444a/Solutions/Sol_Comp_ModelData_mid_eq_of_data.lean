-- Prove2me | solution 1 for Comp.ModelData.mid_eq_of_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:26:21.837001+00:00
-- url     : https://prove2.me/submissions/c9213463-6469-45f4-98f1-242fa7d85876

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_lpre1F_eq
import Theorems.Thm_Comp_ModelData_LW_eq_of_data
import Theorems.Thm_Comp_ModelData_mid_le_of_data
import Theorems.Thm_Comp_CsgQ_lfInner_eq_coe_of_fixed
import Theorems.Thm_Comp_ModelData_Stochastic_nonneg
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
    (hiter : (d.midOf hs k b y)^[m] ∅ = c) (hfix : d.midOf hs k b y c = c) :
    ((d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y).lfp =
      (↑c : Set (Fin d.nStates)) := by
  have hle : (↑c : Set (Fin d.nStates))
      ≤ ((d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y).lfp := by
    have hm := d.mid_le_of_data hs h2 hnz k b y m hlw
    rwa [hiter] at hm
  refine CsgQ.lfInner_eq_coe_of_fixed d.toCsgQ (d.wellFormed hs h2) b y c
    (fun s => (d.lStepOf hs c y s)^[k] ∅)
    (fun s => d.LW_eq_of_data hs h2 hnz k c y s (hlw c s)) ?_ hle
  rw [d.lpre1F_eq hs h2.nonneg hnz]
  exact hfix.symm
end Comp.ModelData
