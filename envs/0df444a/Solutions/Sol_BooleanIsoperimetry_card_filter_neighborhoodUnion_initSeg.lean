-- Prove2me | solution 1 for BooleanIsoperimetry.card_filter_neighborhoodUnion_initSeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:00.791306+00:00
-- url     : https://prove2.me/submissions/353f5aec-940b-404e-9fc5-2eea5f929d6d

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
public import Theorems.Thm_BooleanIsoperimetry_sum_Ico_layerWindowRemainder_max_eq
public import Theorems.Thm_BooleanIsoperimetry_H_le_cube
public import Theorems.Thm_BooleanIsoperimetry_suffix_layerWindowRemainder_eq


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N x y k : ℕ) (hy : y ≤ 2 ^ N) :
    ((neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y).filter
          (fun z => k ≤ z.card)).card
    = max (H N x) y - binomPrefix N k := by
  rw [← sum_Ico_layerWindowRemainder_max_eq]
  exact suffix_layerWindowRemainder_eq N (max (H N x) y) k (max_le (H_le_cube N x) hy)
end BooleanIsoperimetry
