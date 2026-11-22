-- Prove2me | solution 1 for DeciSigma1.Words.ChainBoundFrom.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:43:34.047808+00:00
-- url     : https://prove2.me/submissions/dfd4f3f7-5f2a-4be2-9371-beaa06ecb716

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
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
namespace ChainBoundFrom
theorem _root_.solution {t : List α} {b₀ b₁ Sb Sb' : ℕ} (h : ChainBoundFrom t b₀ Sb)
    (hb : b₀ ≤ b₁) (hS : Sb ≤ Sb') : ChainBoundFrom t b₁ Sb' :=
  fun b bs hb₁ hbs => (h b bs (hb.trans hb₁) hbs).trans hS
end ChainBoundFrom
end DeciSigma1.Words
