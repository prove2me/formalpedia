-- Prove2me | solution 1 for Comp.ModelData.mid_le_of_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:11.801107+00:00
-- url     : https://prove2.me/submissions/df590d42-2234-451e-a4e4-12763d78f8de

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_lpre1F_eq
import Theorems.Thm_Comp_ModelData_LW_eq_of_data
import Theorems.Thm_Comp_CsgQ_le_lfInner_of_step
import Theorems.Thm_Comp_ModelData_Stochastic_nonneg
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (b y : Finset (Fin d.nStates)) (m : ℕ)
    (hlw : ∀ x s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅)
      = (d.lStepOf hs x y s)^[k] ∅) :
    (↑((d.midOf hs k b y)^[m] ∅) : Set (Fin d.nStates))
      ≤ ((d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y).lfp := by
  induction m with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_empty]
      exact bot_le
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      set x := (d.midOf hs k b y)^[m] ∅ with hx
      refine CsgQ.le_lfInner_of_step d.toCsgQ (d.wellFormed hs h2) b y x (d.midOf hs k b y x)
        (fun s => (d.lStepOf hs x y s)^[k] ∅)
        (fun s => d.LW_eq_of_data hs h2 hnz k x y s (hlw x s)) ih ?_
      unfold midOf
      rw [d.lpre1F_eq hs h2.nonneg hnz]
end Comp.ModelData
