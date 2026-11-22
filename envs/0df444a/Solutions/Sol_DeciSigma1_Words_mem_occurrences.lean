-- Prove2me | solution 1 for DeciSigma1.Words.mem_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:47:50.98783+00:00
-- url     : https://prove2.me/submissions/2caa5584-afcc-472a-a767-dc8b7d698c88

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Words.length_suffixOfLength

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]
namespace DeciSigma1.Words
theorem _root_.solution {x t : List α} {b e : ℕ} :
    e ∈ occurrences x t b ↔ e ≤ x.length ∧ b ≤ t.length ∧ suffixOfLength t b <:+ x.take e := by
  simp only [occurrences, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
end DeciSigma1.Words
