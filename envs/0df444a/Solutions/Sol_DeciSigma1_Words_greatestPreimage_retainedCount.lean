-- Prove2me | solution 1 for DeciSigma1.Words.greatestPreimage_retainedCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:46:36.127798+00:00
-- url     : https://prove2.me/submissions/58908cdd-a4fc-48f7-ba10-85659dd6977c

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_lt_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_le_greatestPreimage_iff
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution {p : ℕ} (h : p ∉ D) :
    greatestPreimage D (retainedCount D p) = p := by
  refine le_antisymm (Nat.le_of_not_lt fun hlt => ?_) (le_greatestPreimage_iff.mpr le_rfl)
  have := retainedCount_lt_of_not_mem h hlt
  rw [retainedCount_greatestPreimage] at this
  omega
end DeciSigma1.Words
