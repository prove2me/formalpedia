-- Prove2me | solution 1 for BooleanIsoperimetry.PairLayerWindowCost_eq_zero_of_N_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:09.3253+00:00
-- url     : https://prove2.me/submissions/f46c1c6c-bd40-429c-bd4e-30c89f507014

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_layerWindowRemainder_eq_zero_of_N_lt
public import Theorems.Thm_BooleanIsoperimetry_layerWindowShadowCost_eq_zero_of_N_lt
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution {N r a b : ℕ} (hNr : N < r) :
    PairLayerWindowCost N r a b = 0 := by
  unfold PairLayerWindowCost
  rw [layerWindowShadowCost_eq_zero_of_N_lt hNr,
      layerWindowRemainder_eq_zero_of_N_lt hNr,
      layerWindowShadowCost_eq_zero_of_N_lt hNr,
      layerWindowRemainder_eq_zero_of_N_lt hNr]
  simp
end BooleanIsoperimetry
