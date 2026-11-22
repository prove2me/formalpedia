-- Prove2me | solution 1 for DeciSigma1.Words.suffixReturnGap_le_of_occ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:55:58.740109+00:00
-- url     : https://prove2.me/submissions/69c227e1-fb5f-4114-997f-7e00b8a9ac28

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
theorem _root_.solution {t : List α} {b h : ℕ} (hb : b ≤ t.length) (h1 : 1 ≤ h)
    (h2 : h ≤ t.length)
    (hocc : suffixOfLength t b <:+ t.take (t.length - h)) : ∃ h₀, suffixReturnGap t b = some h₀ ∧
        h₀ ≤
        h := by
  unfold suffixReturnGap
  rw [if_pos hb]
  cases hf : (List.range t.length).find?
      (fun h => suffixOfLength t b <:+ t.take (t.length - (h + 1))) with
  | none =>
    rw [List.find?_eq_none] at hf
    have := hf (h - 1) (List.mem_range.mpr (by omega))
    rw [show h - 1 + 1 = h by omega] at this
    exact absurd (decide_eq_true hocc) this
  | some h0 =>
    refine ⟨h0 + 1, rfl, ?_⟩
    rw [List.find?_range_eq_some] at hf
    by_contra hlt
    have := hf.2.2 (h - 1) (by omega)
    rw [show h - 1 + 1 = h by omega] at this
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact this hocc
end DeciSigma1.Words
