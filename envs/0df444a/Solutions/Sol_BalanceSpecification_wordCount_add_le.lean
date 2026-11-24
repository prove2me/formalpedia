-- Prove2me | solution 1 for BalanceSpecification.wordCount_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:53.253636+00:00
-- url     : https://prove2.me/submissions/4f6d46ff-5a36-4a93-8459-e5906581e082

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution (hL : IsFactorial L) (m n : ℕ) :
    wordCount L (m + n) ≤ wordCount L m * wordCount L n := by
  classical
  rw [wordCount, wordCount, wordCount, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun w : Word A => (w.take m, w.drop m))
  · intro w hw
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
    apply Finset.mem_product.mpr
    constructor
    · apply mem_wordFinset.mpr
      exact ⟨hL (List.take_prefix m w).isInfix hwL,
        by simp only [List.length_take, hwlen]; omega⟩
    · apply mem_wordFinset.mpr
      exact ⟨hL (List.drop_suffix m w).isInfix hwL,
        by simp only [List.length_drop, hwlen]; omega⟩
  · intro v hv w hw h
    have ht := congrArg Prod.fst h
    have hd := congrArg Prod.snd h
    calc
      v = v.take m ++ v.drop m := (List.take_append_drop m v).symm
      _ = w.take m ++ w.drop m := congrArg₂ (fun a b : Word A => a ++ b) ht hd
      _ = w := List.take_append_drop m w
end BalanceSpecification
