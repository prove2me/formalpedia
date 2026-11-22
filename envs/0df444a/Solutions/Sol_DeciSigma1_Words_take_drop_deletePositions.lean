-- Prove2me | solution 1 for DeciSigma1.Words.take_drop_deletePositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:25:24.845514+00:00
-- url     : https://prove2.me/submissions/2dbbe7ba-9674-4fb0-b81d-4981bd598fd5

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_retainedCount
public import Theorems.Thm_P2M_DeciSigma1_Words_getElem__deletePositions_eq_f9d47ab0e923
public import Theorems.Thm_DeciSigma1_Words_not_mem_of_no_junction
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage_add

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) {a n : ℕ}
    (hJ : ∀ p ∈ D, ¬ (a < retainedCount D p ∧ retainedCount D p < a + n)) :
    ((deletePositions w D).drop a).take n = (w.drop (greatestPreimage D a)).take n := by
  have hret := not_mem_of_no_junction hJ
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_take]
  split_ifs with hi
  · rw [List.getElem?_drop, List.getElem?_drop, getElem?_deletePositions_eq,
      ← retainedCount_greatestPreimage_add (fun j hj => hret j (by omega)),
      greatestPreimage_retainedCount (hret i hi)]
  · rfl
end DeciSigma1.Words
