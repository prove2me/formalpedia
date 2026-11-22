-- Prove2me | solution 1 for DeciSigma1.Words.deletePositions_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:49:33.347305+00:00
-- url     : https://prove2.me/submissions/eab7f20b-09a8-4a28-97c1-88b4ba354045

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_P2M_DeciSigma1_Words_getElem__deletePositions_eq_f9d47ab0e923
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Words.greatestPreimage_empty

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) : deletePositions w ∅ = w := by
  apply List.ext_getElem?
  intro a
  rw [getElem?_deletePositions_eq, greatestPreimage_empty]
end DeciSigma1.Words
