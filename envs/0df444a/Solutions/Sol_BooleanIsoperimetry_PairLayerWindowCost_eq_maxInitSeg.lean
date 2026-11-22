-- Prove2me | solution 1 for BooleanIsoperimetry.PairLayerWindowCost_eq_maxInitSeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:56.797409+00:00
-- url     : https://prove2.me/submissions/0177d4c0-bea2-470e-bb32-1c950a9044e9

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
public import Theorems.Thm_BooleanIsoperimetry_layerWindowShadowCost_eq_remainder_H
public import Theorems.Thm_BooleanIsoperimetry_max_layerWindow_eq_union_card
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N r a b : ℕ) :
    PairLayerWindowCost N r a b
      = layerWindowRemainder N r (max (H N a) b)
        + layerWindowRemainder N r (max (H N b) a) := by
  unfold PairLayerWindowCost
  rw [layerWindowShadowCost_eq_remainder_H, layerWindowShadowCost_eq_remainder_H]
  simp only [layerWindowRemainder]
  rw [max_layerWindow_eq_union_card, max_layerWindow_eq_union_card]
end BooleanIsoperimetry
