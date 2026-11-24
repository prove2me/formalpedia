-- Prove2me | solution 1 for BalanceSpecification.IsFactorial.prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:33.12482+00:00
-- url     : https://prove2.me/submissions/a597c487-b162-4ceb-bc6b-7bfe67dd144b

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Synchronization
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
open BalanceSpecification
variable {A : Type*} {L : Set (Word A)}
namespace BalanceSpecification
namespace IsFactorial
theorem _root_.solution (hL : IsFactorial L) {u v : Word A}
    (h : u ++ v ∈ L) : u ∈ L := by
  apply hL (u := u) (v := u ++ v) _ h
  exact ⟨[], v, by simp only [List.nil_append]⟩
end IsFactorial
end BalanceSpecification
