-- Prove2me | solution 1 for DeciSigma1.Words.suffixReturnGap_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:26.282795+00:00
-- url     : https://prove2.me/submissions/c33a8493-24e5-4593-8e08-1532a908b4f2

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
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
theorem _root_.solution {t : List α} {b h : ℕ} (hD : suffixReturnGap t b = some h) :
    b ≤ t.length ∧ 1 ≤ h ∧ b + h ≤ t.length ∧ suffixOfLength t b <:+ t.take (t.length - h) := by
  unfold suffixReturnGap at hD
  split_ifs at hD with hb
  obtain ⟨h0, hf, rfl⟩ := Option.map_eq_some_iff.mp hD
  rw [List.find?_range_eq_some] at hf
  obtain ⟨h1, h2, _⟩ := hf
  simp only [List.mem_range, decide_eq_true_eq] at h1 h2
  refine ⟨hb, by omega, ?_, h1⟩
  have := h1.length_le
  simp only [length_suffixOfLength, List.length_take] at this
  omega
end DeciSigma1.Words
