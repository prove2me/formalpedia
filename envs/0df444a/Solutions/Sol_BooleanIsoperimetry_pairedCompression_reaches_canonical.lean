-- Prove2me | solution 1 for BooleanIsoperimetry.pairedCompression_reaches_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:47:45.493749+00:00
-- url     : https://prove2.me/submissions/cc484f90-b2fd-4e68-8d7d-77eb18a162e2

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
public import Theorems.Thm_BooleanIsoperimetry_compress_to_simplicial_pair
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_reaches_canonical
public import Theorems.Thm_BooleanIsoperimetry_card_le_two_pow


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A B : Finset (Cube N)) :
    ∃ A' B' : Finset (Cube N), IsCanonicalCascadePair A' B' ∧
      A'.card + B'.card = A.card + B.card ∧
      PairShadowCost N A' B' ≤ PairShadowCost N A B := by
  have hphase1 :
      PairShadowCost N (simplicialInitSeg N A.card) (simplicialInitSeg N B.card)
        ≤ PairShadowCost N A B := compress_to_simplicial_pair A B
  obtain ⟨A', B', hcan, htot, hphase2⟩ :=
    cascade_split_reaches_canonical A.card B.card (card_le_two_pow A) (card_le_two_pow B)
  exact ⟨A', B', hcan, htot, le_trans hphase2 hphase1⟩
end BooleanIsoperimetry
