-- Prove2me | solution 1 for DeciSigma1.Words.ChainBound.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:43:26.123796+00:00
-- url     : https://prove2.me/submissions/be5e8918-cfae-406f-8f3f-41282df82e52

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
namespace ChainBound
theorem _root_.solution {t : List α} {Sb Sb' : ℕ}
    (h : ChainBound t Sb)
    (hS : Sb ≤ Sb') : ChainBound t Sb' :=
  fun bs hbs => (h bs hbs).trans (by omega)
end ChainBound
end DeciSigma1.Words
