-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixNode_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:51:19.162818+00:00
-- url     : https://prove2.me/submissions/cd5f381c-2de3-4f5b-9963-93db8e89db67

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_take_append_suffix
public import Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_suffix
public import Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_snoc
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
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
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (T : Table α S k) (q0 : S) (hD : [] ∈ D)
    (hpre : ∀ u a, u ++ [a] ∈ D → u ∈ D) (w : List α) (a : α) :
    suffixNode T q0 D (w ++ [a]) = suffixNodeStep T D (suffixNode T q0 D w) a := by
  have hsnoc := dictSuffix_snoc hD hpre w a
  simp only [suffixNode, suffixNodeStep, ← hsnoc]
  refine Prod.ext rfl ?_
  simp only
  have hs := dictSuffix_suffix D w
  have hsw := hs.length_le
  have h2 : (dictSuffix D (w ++ [a])).length ≤ (dictSuffix D w).length + 1 := by
    rw [hsnoc]; simpa using (dictSuffix_suffix D (dictSuffix D w ++ [a])).length_le
  generalize dictSuffix D (w ++ [a]) = s' at h2 ⊢
  generalize dictSuffix D w = s at hs hsw h2 ⊢
  have e : w ++ [a] = w.take (w.length - s.length) ++ (s ++ [a]) := by
    rw [← List.append_assoc, take_append_suffix hs]
  rw [← runFrom_append, e, List.take_append, List.take_of_length_le (by simp; omega)]
  congr 3
  simp
  omega
end DeciSigma1.Holes.Tail
