-- Prove2me | solution 1 for DeciSigma1.Words.chainBound_len
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:40:20.981647+00:00
-- url     : https://prove2.me/submissions/c7374abe-4e59-47fc-90d6-886e52b2e4c7

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_pairwise
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
theorem _root_.solution (t : List α) : ChainBound t t.length := by
  intro bs h
  match bs, h with
  | [], _ => simp
  | b0 :: rest, h =>
    have hp := (List.pairwise_cons.mp h.pairwise)
    have hsub : rest.toFinset ⊆ Finset.Icc 1 t.length := by
      intro b hb
      have := hp.1 b (List.mem_toFinset.mp hb)
      simp only [Finset.mem_Icc]; omega
    have hnd : rest.Nodup := hp.2.imp fun h => Nat.ne_of_lt h.1
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, Nat.card_Icc] at this
    simp only [List.length_cons]
    omega
end DeciSigma1.Words
