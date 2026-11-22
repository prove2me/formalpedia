-- Prove2me | solution 1 for DeciSigma1.Words.SuffixStep.spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:49:43.546434+00:00
-- url     : https://prove2.me/submissions/0c4caf43-4a4e-409f-bc5d-63aec4fc702b

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_suffixReturnGap_spec
public import Theorems.Thm_DeciSigma1_Words_suffixOfLength_prefix_of_suffixReturnGap

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]
namespace DeciSigma1.Words
namespace SuffixStep
theorem _root_.solution {t : List α} {b b' : ℕ} (h : SuffixStep t b b') :
    b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b' := by
  obtain ⟨hD, hlt⟩ := h
  have := suffixReturnGap_spec hD
  refine ⟨hlt, by omega, ?_⟩
  have h' := suffixOfLength_prefix_of_suffixReturnGap hD
  rwa [show b + (b' - b) = b' by omega] at h'
end SuffixStep
end DeciSigma1.Words
