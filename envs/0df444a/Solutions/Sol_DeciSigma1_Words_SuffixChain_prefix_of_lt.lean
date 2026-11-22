-- Prove2me | solution 1 for DeciSigma1.Words.SuffixChain.prefix_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:59:38.26701+00:00
-- url     : https://prove2.me/submissions/965f0fd7-fb5d-44cb-863d-01bbb4e9c94b

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_pairwise

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]
namespace DeciSigma1.Words
namespace SuffixChain
theorem _root_.solution {t : List α} {bs : List ℕ}
    (h : SuffixChain t bs)
    {b b' : ℕ} (hb : b ∈ bs) (hb' : b' ∈ bs) (hlt : b < b') : suffixOfLength t b <+:
        suffixOfLength t b' := by
  have hp := List.pairwise_iff_getElem.mp h.pairwise
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hb'
  rcases lt_trichotomy j j' with h1 | rfl | h1
  · exact (hp j j' hj hj' h1).2.2
  · omega
  · exact absurd (hp j' j hj' hj h1).1 (by omega)
end SuffixChain
end DeciSigma1.Words
