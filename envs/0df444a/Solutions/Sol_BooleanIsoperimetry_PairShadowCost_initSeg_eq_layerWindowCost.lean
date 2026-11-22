-- Prove2me | solution 1 for BooleanIsoperimetry.PairShadowCost_initSeg_eq_layerWindowCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:25.165708+00:00
-- url     : https://prove2.me/submissions/4d5fb554-3680-4caf-8e3a-6c7a6b48a38b

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_PairShadowCost_initSeg_eq_max_H
public import Theorems.Thm_BooleanIsoperimetry_neighborhoodLayerCost_eq_H


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    {N a b : ℕ} (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    PairShadowCost N (simplicialInitSeg N a) (simplicialInitSeg N b) =
      initSegPairLayerWindowCost N a b := by
  rw [PairShadowCost_initSeg_eq_max_H ha hb]
  unfold initSegPairLayerWindowCost
  rw [neighborhoodLayerCost_eq_H, neighborhoodLayerCost_eq_H]
end BooleanIsoperimetry
