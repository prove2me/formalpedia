-- Prove2me | solution 1 for DeciSigma1.Words.chainBound_mortal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:50:28.057799+00:00
-- url     : https://prove2.me/submissions/56bde188-6a17-46d7-98a7-9927b37c3767

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_chain_length_le_mortal
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]
variable {S : Type} [Fintype S] {k : ℕ} (M : StructuralReader α S k)
  {W : Fin k → List α} {j : Fin k}
variable {M}
namespace DeciSigma1.Words
theorem _root_.solution (h : M.Eligible W j) (hm : ¬ M.Immortal (M.endState W j)) :
    ChainBound (W j) (Fintype.card S - 1) :=
  fun _ hbs => (chain_length_le_mortal h hm hbs).trans (Nat.le_succ _)
end DeciSigma1.Words
