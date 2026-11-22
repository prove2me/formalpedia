-- Prove2me | solution 1 for DeciSigma1.Words.occurrences_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:07.002608+00:00
-- url     : https://prove2.me/submissions/b4cc806a-e5b5-4879-b2d6-833efdfd1b4b

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_suffixOfLength_suffix_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_mem_occurrences
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]
namespace DeciSigma1.Words
theorem _root_.solution {x t : List α} {b b' : ℕ} (h : b ≤ b') :
    occurrences x t b' ⊆ occurrences x t b := by
  intro e he
  rw [mem_occurrences] at he ⊢
  exact ⟨he.1, h.trans he.2.1, (suffixOfLength_suffix_suffixOfLength t h).trans he.2.2⟩
end DeciSigma1.Words
