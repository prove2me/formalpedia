-- Prove2me | solution 1 for BalanceSpecification.wordCount_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:39.515625+00:00
-- url     : https://prove2.me/submissions/cd8d462d-c477-4941-a3f6-8e4eeb30829a

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Theorems.Thm_BalanceSpecification_mem_avoidingLanguage
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


attribute [local simp] BalanceSpecification.mem_avoidingLanguage

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution (hL : IsFactorial L) {m n : ℕ}
    (hm : wordCount L m = 0) (hmn : m ≤ n) : wordCount L n = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
  have htake : w.take m ∈ wordFinset L m := mem_wordFinset.mpr
    ⟨hL (List.take_prefix m w).isInfix hwL,
      by simp only [List.length_take, hwlen, Nat.min_eq_left hmn]⟩
  have hempty : wordFinset L m = ∅ := Finset.card_eq_zero.mp hm
  rw [hempty] at htake
  exact Finset.notMem_empty _ htake
end BalanceSpecification
