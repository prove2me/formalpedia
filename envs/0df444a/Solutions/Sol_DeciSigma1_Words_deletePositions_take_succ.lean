-- Prove2me | solution 1 for DeciSigma1.Words.deletePositions_take_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:45:54.373455+00:00
-- url     : https://prove2.me/submissions/5e46c519-61e8-42dc-9e0d-c5305bbeb28e

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_snoc
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) (c : ℕ) :
    deletePositions (w.take (c + 1)) D = deletePositions (w.take c) D ++ if c ∈
        D then [] else (w[c]?).toList := by
  rw [List.take_add_one]
  rcases Nat.lt_or_ge c w.length with hc | hc
  · rw [List.getElem?_eq_getElem hc, Option.toList_some, deletePositions_snoc, List.length_take,
      min_eq_left hc.le]
  · rw [List.getElem?_eq_none hc, Option.toList_none, List.append_nil]
    split_ifs <;> simp
end DeciSigma1.Words
