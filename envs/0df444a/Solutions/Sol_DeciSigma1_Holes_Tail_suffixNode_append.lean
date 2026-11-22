-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixNode_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:50:45.802236+00:00
-- url     : https://prove2.me/submissions/9ca807af-b9ce-4eb5-9a2f-cf79f0a207b2

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_suffix
public import Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_mem
public import Theorems.Thm_DeciSigma1_Holes_Tail_length_le_length_dictSuffix
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
public import Theorems.Thm_DeciSigma1_runFrom_append
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
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (T : Table α S k) (q0 : S) (hD : [] ∈ D) {u v : List α}
    (hB : ∀ r ∈ D, r.length ≤ v.length) :
    suffixNode T q0 D (u ++ v) = (dictSuffix D v, runFrom T.step (runFrom T.step q0 u)
      (v.take (v.length - (dictSuffix D v).length))) := by
  have hdv : dictSuffix D (u ++ v) = dictSuffix D v := by
    apply dictSuffix_eq hD ((dictSuffix_suffix D v).trans (List.suffix_append _ _))
      (dictSuffix_mem hD v)
    intro r hr hrD
    exact length_le_length_dictSuffix
      (List.suffix_of_suffix_length_le hr (List.suffix_append _ _) (hB r hrD)) hrD
  simp only [suffixNode, hdv]
  have := (dictSuffix_suffix D v).length_le
  rw [← runFrom_append, List.take_append, List.take_of_length_le (by simp; omega)]
  congr 3
  simp
  omega
end DeciSigma1.Holes.Tail
