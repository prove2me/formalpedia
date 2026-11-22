-- Prove2me | solution 1 for DeciSigma1.Words.SuffixChain.le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:50:57.513796+00:00
-- url     : https://prove2.me/submissions/183a1014-0d9f-4f12-9f60-8bf6ffbb6b4d

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
theorem _root_.solution {t : List α} {bs : List ℕ} (h : SuffixChain t bs)
    (h2 : 2 ≤ bs.length) :
    ∀ b ∈ bs, b ≤ t.length := by
  match bs, h, h2 with
  | b0 :: b1 :: rest, h, _ =>
    have hp := (List.pairwise_cons.mp h.pairwise).1
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · have := hp b1 List.mem_cons_self; omega
    · exact (hp b hb).2.1
end SuffixChain
end DeciSigma1.Words
