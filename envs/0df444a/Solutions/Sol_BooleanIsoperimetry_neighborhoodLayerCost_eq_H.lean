-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhoodLayerCost_eq_H
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:14.169801+00:00
-- url     : https://prove2.me/submissions/06cec12c-fe04-4956-b7a1-adf8bf41cdaf

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution (N a : ℕ) :
    neighborhoodLayerCost N a = H N a := by
  unfold neighborhoodLayerCost layerCount layerPart H
  symm
  exact Finset.card_eq_sum_card_fiberwise (f := fun x : Cube N => x.card)
    (t := Finset.range (N + 2))
    (fun x _ => by
      simp only [Finset.coe_range, Set.mem_Iio]
      have hle : x.card ≤ N := by
        have := Finset.card_le_univ x
        simpa [Fintype.card_fin] using this
      omega)
end BooleanIsoperimetry
