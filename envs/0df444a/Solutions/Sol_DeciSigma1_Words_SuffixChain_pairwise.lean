-- Prove2me | solution 1 for DeciSigma1.Words.SuffixChain.pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:50:19.711203+00:00
-- url     : https://prove2.me/submissions/78caf2d6-867a-4721-9236-5145d72a399e

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_SuffixStep_spec
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
namespace SuffixChain
theorem _root_.solution {t : List α} {bs : List ℕ} (h : SuffixChain t bs) :
    bs.Pairwise
        (fun b b' => b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b') := by
  unfold SuffixChain at h
  have htrans : ∀ a b c : ℕ, (a < b ∧ b ≤ t.length ∧ suffixOfLength t a <+: suffixOfLength t b) →
      (b < c ∧ c ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t c) →
      (a < c ∧ c ≤ t.length ∧ suffixOfLength t a <+: suffixOfLength t c) :=
    fun a b c h1 h2 => ⟨h1.1.trans h2.1, h2.2.1, h1.2.2.trans h2.2.2⟩
  have hc : bs.IsChain
      (fun b b' => b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b') :=
    h.imp fun b b' hs => hs.spec
  have : Trans (fun b b' : ℕ => b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b')
      (fun b b' : ℕ => b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b')
      (fun b b' : ℕ => b < b' ∧ b' ≤ t.length ∧ suffixOfLength t b <+: suffixOfLength t b') :=
    ⟨fun h1 h2 => htrans _ _ _ h1 h2⟩
  exact List.isChain_iff_pairwise.mp hc
end SuffixChain
end DeciSigma1.Words
