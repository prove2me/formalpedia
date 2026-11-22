-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixNode_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:50:03.453299+00:00
-- url     : https://prove2.me/submissions/9e126737-ebcb-4017-a19d-4b1ddf4ce74c

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffix_dictSuffix
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
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
theorem _root_.solution (T : Table α S k) (q0 : S) {w p : List α} (hp : p <:+ w)
    (hpD : p ∈ D) :
    p <:+ (suffixNode T q0 D w).1 ∧
      runFrom T.step q0 (w.take (w.length - p.length)) =
        runFrom T.step (suffixNode T q0 D w).2
          ((suffixNode T q0 D w).1.take ((suffixNode T q0 D w).1.length - p.length)) := by
  have hps := suffix_dictSuffix hp hpD
  refine ⟨hps, ?_⟩
  simp only [suffixNode]
  have hpl := hps.length_le
  have hs := dictSuffix_suffix D w
  have hsw := hs.length_le
  generalize dictSuffix D w = s at hs hsw hpl ⊢
  have e : w = w.take (w.length - s.length) ++ s := (take_append_suffix hs).symm
  rw [← runFrom_append]
  conv_lhs => rw [e]
  rw [List.take_append, List.take_of_length_le (by simp; omega)]
  congr 3
  simp
  omega
end DeciSigma1.Holes.Tail
