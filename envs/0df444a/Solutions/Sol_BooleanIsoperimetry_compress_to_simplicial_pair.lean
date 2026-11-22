-- Prove2me | solution 1 for BooleanIsoperimetry.compress_to_simplicial_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:47:00.791634+00:00
-- url     : https://prove2.me/submissions/a487fc0d-0a86-48f9-a957-518c94c83551

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
public import Theorems.Thm_BooleanIsoperimetry_simplicialInitSeg_neighborhood_card_min
public import Theorems.Thm_BooleanIsoperimetry_card_le_two_pow
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A B : Finset (Cube N)) :
    PairShadowCost N (simplicialInitSeg N A.card) (simplicialInitSeg N B.card)
      ≤ PairShadowCost N A B := by
  unfold PairShadowCost
  have hNA := simplicialInitSeg_neighborhood_card_min A
  have hNB := simplicialInitSeg_neighborhood_card_min B
  have hAcard : (simplicialInitSeg N A.card).card = A.card := by
    rw [card_simplicialInitSeg]; exact min_eq_left (card_le_two_pow A)
  have hBcard : (simplicialInitSeg N B.card).card = B.card := by
    rw [card_simplicialInitSeg]; exact min_eq_left (card_le_two_pow B)
  rw [hAcard, hBcard]
  exact Nat.add_le_add (max_le_max hNA le_rfl) (max_le_max hNB le_rfl)
end BooleanIsoperimetry
