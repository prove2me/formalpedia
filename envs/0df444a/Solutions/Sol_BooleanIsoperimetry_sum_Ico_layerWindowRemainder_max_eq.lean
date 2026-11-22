-- Prove2me | solution 1 for BooleanIsoperimetry.sum_Ico_layerWindowRemainder_max_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:21.409896+00:00
-- url     : https://prove2.me/submissions/77252911-ef98-491c-9c12-2708ac5a2b7f

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
public import Theorems.Thm_BooleanIsoperimetry_initSeg_nested
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_initSeg_eq
public import Theorems.Thm_BooleanIsoperimetry_sum_Ico_layerCount_eq_filter_card_ge


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N x y k : ℕ) :
    ∑ r ∈ Finset.Ico k (N + 2), layerWindowRemainder N r (max (H N x) y)
      = ((neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y).filter
          (fun z => k ≤ z.card)).card := by
  have hset : neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y
      = simplicialInitSeg N (max (H N x) y) := by
    rw [neighborhood_initSeg_eq]
    rcases le_total (H N x) y with h | h
    · rw [max_eq_right h, Finset.union_eq_right.mpr (initSeg_nested h)]
    · rw [max_eq_left h, Finset.union_eq_left.mpr (initSeg_nested h)]
  rw [hset,
      ← sum_Ico_layerCount_eq_filter_card_ge N k (simplicialInitSeg N (max (H N x) y))]
  rfl
end BooleanIsoperimetry
