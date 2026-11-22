-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.dictSuffix_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:50:33.506239+00:00
-- url     : https://prove2.me/submissions/b485226b-695c-40f6-8415-c28fc6364ddb

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Holes_Tail_snoc_suffix_snoc_iff
public import Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_suffix
public import Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_mem
public import Theorems.Thm_DeciSigma1_Holes_Tail_length_le_length_dictSuffix
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffix_dictSuffix
public import Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_eq
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] {D : Finset (List α)}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (hD : [] ∈ D) (hpre : ∀ u a, u ++ [a] ∈ D → u ∈ D) (w : List α)
    (a : α) : dictSuffix D (w ++ [a]) = dictSuffix D (dictSuffix D w ++ [a]) := by
  apply dictSuffix_eq hD ((dictSuffix_suffix D _).trans
    (snoc_suffix_snoc_iff.mpr ⟨dictSuffix_suffix D w, rfl⟩)) (dictSuffix_mem hD _)
  intro r hr hrD
  rcases List.eq_nil_or_concat r with rfl | ⟨r0, b, rfl⟩
  · simp
  · rw [List.concat_eq_append] at hr hrD ⊢
    obtain ⟨hr0, rfl⟩ := snoc_suffix_snoc_iff.mp hr
    exact length_le_length_dictSuffix
      (snoc_suffix_snoc_iff.mpr ⟨suffix_dictSuffix hr0 (hpre r0 _ hrD), rfl⟩) hrD
end DeciSigma1.Holes.Tail
