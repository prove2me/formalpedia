-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixChain_mem_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:06:11.07572+00:00
-- url     : https://prove2.me/submissions/36313ca7-8833-4731-abd7-eb77b9912682

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_suffixChain_getElem__eq_of_mem_b81ca86b8910
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_mem_occurrences
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__suffixOfLength_5cd134b71b98
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {t : List α} {b b₀ b' : ℕ} {bs : List ℕ}
    (h : SuffixChain t (b₀ :: bs)) (hb : b ≤ b₀) (hb' : b' ∈ b₀ :: bs) (hle : b' ≤ t.length) :
    t.length - b' + b₀ ∈ occurrences t t b := by
  obtain ⟨hbb, htext⟩ := suffixChain_getElem?_eq_of_mem h hb' hle
  rw [mem_occurrences]
  refine ⟨by omega, by omega, ?_⟩
  have hl : (suffixOfLength t b).length = b := by simp; omega
  rw [suffix_take_iff (by omega), hl]
  refine ⟨by omega, fun j hj => ?_⟩
  rw [getElem?_suffixOfLength, show t.length - b' + b₀ - b + j = t.length - b' + (b₀ - b + j) by
    omega, htext _ (by omega)]
  congr 1; omega
end DeciSigma1.Holes.Tail
