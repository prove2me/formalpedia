-- Prove2me | solution 1 for BooleanIsoperimetry.card_filter_neighborhoodUnion_initSeg_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:01.280981+00:00
-- url     : https://prove2.me/submissions/9dfeeebe-48e9-4bbc-b3ea-b6c935ebcdc4

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
public import Theorems.Thm_BooleanIsoperimetry_suffix_layerWindowRemainder_eq
public import Theorems.Thm_BooleanIsoperimetry_sum_Ico_layerCount_eq_filter_card_ge


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N x y z k : ℕ)
    (h_le : H N x ≤ y) (hy : y ≤ 2 ^ N) (hz : z ≤ 2 ^ N) :
    ((neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y ∪ simplicialInitSeg N z).filter
          (fun z => k ≤ z.card)).card
    = max y z - binomPrefix N k := by
  have hset : neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y ∪ simplicialInitSeg N z
      = simplicialInitSeg N (max y z) := by
    rw [neighborhood_initSeg_eq]
    rw [Finset.union_eq_right.mpr (initSeg_nested h_le)]
    rcases le_total y z with hyz | hzy
    · rw [max_eq_right hyz, Finset.union_eq_right.mpr (initSeg_nested hyz)]
    · rw [max_eq_left hzy, Finset.union_eq_left.mpr (initSeg_nested hzy)]
  rw [hset, ← sum_Ico_layerCount_eq_filter_card_ge N k (simplicialInitSeg N (max y z))]
  exact suffix_layerWindowRemainder_eq N (max y z) k (max_le hy hz)
end BooleanIsoperimetry
