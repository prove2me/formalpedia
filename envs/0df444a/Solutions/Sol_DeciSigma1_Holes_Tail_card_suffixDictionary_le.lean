-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.card_suffixDictionary_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:41:06.304885+00:00
-- url     : https://prove2.me/submissions/8696996f-3eec-4763-83ed-68e3fdf089b9

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_nonemptyFactors_le
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
variable [DecidableEq α]
variable {ts : List (List α)} {B : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (ts : List (List α)) (B : ℕ) :
    (suffixDictionary ts B).card ≤ ts.length * (B * (B + 1) / 2) + 1 := by
  refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
  have hB : ∀ t : List α, (Words.suffixOfLength t B).length ≤ B := fun t => by simp
  calc _ ≤ ∑ t ∈ ts.toFinset, (nonemptyFactors (Words.suffixOfLength t B)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ ts.toFinset, B * (B + 1) / 2 := Finset.sum_le_sum fun t _ =>
        (card_nonemptyFactors_le _).trans (Nat.div_le_div_right
          (Nat.mul_le_mul (hB t) (Nat.add_le_add_right (hB t) 1)))
    _ = ts.toFinset.card * (B * (B + 1) / 2) := by simp
    _ ≤ ts.length * (B * (B + 1) / 2) := Nat.mul_le_mul_right _ (List.toFinset_card_le ts)
end DeciSigma1.Holes.Tail
