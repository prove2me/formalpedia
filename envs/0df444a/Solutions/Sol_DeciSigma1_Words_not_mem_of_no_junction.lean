-- Prove2me | solution 1 for DeciSigma1.Words.not_mem_of_no_junction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:50:20.260801+00:00
-- url     : https://prove2.me/submissions/566e0851-9991-45c7-905d-abc4b1bb7c8f

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_Words_retainedCount_lt_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_le
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_not_mem
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
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
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.deletePositions_empty

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution {a n : ℕ}
    (hJ : ∀ p ∈ D, ¬ (a < retainedCount D p ∧ retainedCount D p < a + n)) :
    ∀ i < n, greatestPreimage D a + i ∉ D := by
  intro i hi hm
  have h0 : i ≠ 0 := fun h => greatestPreimage_not_mem a (by simpa [h] using hm)
  have h1 := retainedCount_add_le (D := D) (greatestPreimage D a) i
  have h2 := retainedCount_lt_of_not_mem (greatestPreimage_not_mem (D := D) a)
    (show greatestPreimage D a < greatestPreimage D a + i by omega)
  rw [retainedCount_greatestPreimage] at h1 h2
  exact hJ _ hm ⟨h2, by omega⟩
end DeciSigma1.Words
