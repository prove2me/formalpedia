-- Prove2me | solution 1 for BooleanIsoperimetry.initSegPairLayerWindowCost_eq_KK_window_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:16.774743+00:00
-- url     : https://prove2.me/submissions/ce5cd7a3-86db-4a0b-b897-d71cb7416cc5

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_neighborhoodLayerCost_eq_H
public import Theorems.Thm_BooleanIsoperimetry_sum_max_shadowRemainder

set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution (N a b : ℕ)
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    initSegPairLayerWindowCost N a b =
      ∑ r ∈ Finset.range (N + 2), PairLayerWindowCost N r a b := by
  unfold initSegPairLayerWindowCost PairLayerWindowCost
  rw [Finset.sum_add_distrib, sum_max_shadowRemainder N a b hb,
      sum_max_shadowRemainder N b a ha, neighborhoodLayerCost_eq_H,
      neighborhoodLayerCost_eq_H]
end BooleanIsoperimetry
