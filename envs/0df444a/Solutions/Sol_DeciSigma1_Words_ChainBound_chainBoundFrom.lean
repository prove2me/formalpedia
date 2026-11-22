-- Prove2me | solution 1 for DeciSigma1.Words.ChainBound.chainBoundFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:04.95751+00:00
-- url     : https://prove2.me/submissions/7b49e434-f77e-4c95-bf63-43b74ae97fa7

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
namespace ChainBound
theorem _root_.solution {t : List α} {Sb : ℕ} (h : ChainBound t Sb) (b₀ : ℕ) :
    ChainBoundFrom t b₀ Sb := fun _ _ _ hbs => by
  have := h _ hbs
  simp only [List.length_cons] at this
  omega
end ChainBound
end DeciSigma1.Words
