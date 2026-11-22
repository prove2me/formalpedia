-- Prove2me | solution 1 for BooleanIsoperimetry.PairShadowCost_le_neighborhood_embeddedPair_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:19.278809+00:00
-- url     : https://prove2.me/submissions/b165b9d5-fc02-47bf-b606-5fb2b229243b

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
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_embeddedPair_card

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A B : Finset (Cube N)) :
    PairShadowCost N A B ≤ (neighborhood 1 (embeddedPair N A B)).card := by
  rw [neighborhood_embeddedPair_card]
  unfold PairShadowCost
  have hA : max (neighborhood 1 A).card B.card ≤ (neighborhood 1 A ∪ B).card := by
    exact max_le (Finset.card_le_card (by intro x hx; exact Finset.mem_union_left _ hx))
      (Finset.card_le_card (by intro x hx; exact Finset.mem_union_right _ hx))
  have hB : max (neighborhood 1 B).card A.card ≤ (neighborhood 1 B ∪ A).card := by
    exact max_le (Finset.card_le_card (by intro x hx; exact Finset.mem_union_left _ hx))
      (Finset.card_le_card (by intro x hx; exact Finset.mem_union_right _ hx))
  exact Nat.add_le_add hA hB
end BooleanIsoperimetry
