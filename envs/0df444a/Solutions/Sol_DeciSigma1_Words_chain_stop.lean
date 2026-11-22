-- Prove2me | solution 1 for DeciSigma1.Words.chain_stop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:49:39.461724+00:00
-- url     : https://prove2.me/submissions/0de57825-2ab6-41fd-a201-7a4be082ccf9

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_ChainBound_chainBoundFrom
public import Theorems.Thm_DeciSigma1_Words_chain_stop_from

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]
namespace DeciSigma1.Words
theorem _root_.solution {t : List α} {S : ℕ} (hS : ChainBound t S) (g : ℕ → ℕ) (hg : Monotone g)
    (bs : ℕ) : ∃ b, bs ≤ b ∧ b ≤ (fun b => b + g b)^[S] bs ∧
      ∀ h, suffixReturnGap t b = some h → g b < h :=
  chain_stop_from (hS.chainBoundFrom bs) g hg le_rfl
end DeciSigma1.Words
