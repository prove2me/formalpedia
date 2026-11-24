-- Prove2me | solution 1 for BalanceSpecification.shiftMap_iterate_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:09.322784+00:00
-- url     : https://prove2.me/submissions/9f1a45db-2cb3-44dd-8817-41dd5f69ba30

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
omit [Fintype A]
namespace BalanceSpecification
theorem _root_.solution (X : ShiftSpace A) (x : X.carrier) (n : ℕ) :
    ((shiftMap X)^[n] x).val = SymbolicDynamics.FullShift.shift (n : ℤ) x.val := by
  induction n with
  | zero =>
    funext i
    simp only [Function.iterate_zero, id_eq, SymbolicDynamics.FullShift.shift_apply, Nat.cast_zero,
      zero_add]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change SymbolicDynamics.FullShift.shift 1 ((shiftMap X)^[n] x).val = _
    rw [ih]
    funext i
    simp only [SymbolicDynamics.FullShift.shift_apply, Nat.cast_succ]
    rw [add_assoc]
end BalanceSpecification
