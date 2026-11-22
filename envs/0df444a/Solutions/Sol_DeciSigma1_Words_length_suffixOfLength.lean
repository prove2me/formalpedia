-- Prove2me | solution 1 for DeciSigma1.Words.length_suffixOfLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:42:24.188823+00:00
-- url     : https://prove2.me/submissions/1f4edc53-e55d-4a5c-b90a-e1675bdeaa86

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
namespace DeciSigma1.Words
theorem _root_.solution (t : List α) (b : ℕ) :
    (suffixOfLength t b).length = min b t.length := by
  simp only [suffixOfLength, List.length_drop]; omega
end DeciSigma1.Words
