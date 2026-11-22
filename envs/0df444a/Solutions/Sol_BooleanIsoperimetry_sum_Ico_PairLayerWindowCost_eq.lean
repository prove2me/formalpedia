-- Prove2me | solution 1 for BooleanIsoperimetry.sum_Ico_PairLayerWindowCost_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:52.665187+00:00
-- url     : https://prove2.me/submissions/ad9d79a5-ff9d-4d8f-9108-e4671673e2a7

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
public import Theorems.Thm_BooleanIsoperimetry_PairLayerWindowCost_eq_maxInitSeg
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
theorem _root_.solution (N a b k : ℕ)
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    ∑ r ∈ Finset.Ico k (N + 2), PairLayerWindowCost N r a b
      = (max (H N a) b - binomPrefix N k) + (max (H N b) a - binomPrefix N k) := by
  have hMa : max (H N a) b ≤ 2 ^ N := max_le (H_le_cube N a) hb
  have hMb : max (H N b) a ≤ 2 ^ N := max_le (H_le_cube N b) ha
  rw [Finset.sum_congr rfl (fun r _ => PairLayerWindowCost_eq_maxInitSeg N r a b),
      Finset.sum_add_distrib,
      suffix_layerWindowRemainder_eq N (max (H N a) b) k hMa,
      suffix_layerWindowRemainder_eq N (max (H N b) a) k hMb]
end BooleanIsoperimetry
