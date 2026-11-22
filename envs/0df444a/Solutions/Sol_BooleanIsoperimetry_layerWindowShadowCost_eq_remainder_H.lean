-- Prove2me | solution 1 for BooleanIsoperimetry.layerWindowShadowCost_eq_remainder_H
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:59.917859+00:00
-- url     : https://prove2.me/submissions/c8c83381-bde7-434f-af80-63b009501768

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_layerCount_neighborhood_initSeg

set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution (N r a : ℕ) :
    layerWindowShadowCost N r a = layerWindowRemainder N r (H N a) := by
  unfold layerWindowShadowCost layerWindowRemainder
  rw [layerCount_neighborhood_initSeg]
end BooleanIsoperimetry
