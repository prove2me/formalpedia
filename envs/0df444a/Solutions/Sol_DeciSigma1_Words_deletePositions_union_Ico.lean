-- Prove2me | solution 1 for DeciSigma1.Words.deletePositions_union_Ico
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:49:33.879791+00:00
-- url     : https://prove2.me/submissions/f95faf60-2906-4bbb-b58b-2ba823271f02

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_P2M_DeciSigma1_Words_getElem__deletePositions_eq_f9d47ab0e923
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_union_Ico

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
variable {c δ : ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) (hD : ∀ p ∈ D, p < c) (hc : c ≤ w.length) :
    deletePositions w (D ∪ Finset.Ico c (c + δ)) =
      deletePositions (w.take c ++ w.drop (c + δ)) D := by
  apply List.ext_getElem?
  intro a
  rw [getElem?_deletePositions_eq, getElem?_deletePositions_eq, greatestPreimage_union_Ico hD]
  have hl : (w.take c).length = c := by rw [List.length_take, min_eq_left hc]
  split_ifs with h
  · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop, hl]
    congr 1
    omega
end DeciSigma1.Words
