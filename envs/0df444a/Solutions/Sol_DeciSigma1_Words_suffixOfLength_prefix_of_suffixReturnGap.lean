-- Prove2me | solution 1 for DeciSigma1.Words.suffixOfLength_prefix_of_suffixReturnGap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:49:19.828805+00:00
-- url     : https://prove2.me/submissions/a7d61cba-724f-4709-ba41-0c7631307747

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_suffixReturnGap_spec
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
theorem _root_.solution {t : List α} {b h : ℕ}
    (hD : suffixReturnGap t b = some h) :
    suffixOfLength t b <+: suffixOfLength t (b + h) := by
  obtain ⟨hb, h1, h2, hocc⟩ := suffixReturnGap_spec hD
  obtain ⟨u, hu⟩ := hocc
  have hlen : u.length = t.length - h - b := by
    have := congrArg List.length hu
    simp only [List.length_append, length_suffixOfLength, List.length_take] at this
    omega
  have e : suffixOfLength t b = (t.take (t.length - h)).drop (t.length - h - b) := by
    rw [← hu, ← hlen, List.drop_left]
  rw [e, List.drop_take]
  unfold suffixOfLength
  rw [show t.length - h - b = t.length - (b + h) by omega]
  exact List.take_prefix _ _
end DeciSigma1.Words
