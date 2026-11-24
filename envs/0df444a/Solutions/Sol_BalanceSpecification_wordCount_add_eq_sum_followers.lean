-- Prove2me | solution 1 for BalanceSpecification.wordCount_add_eq_sum_followers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:16.727935+00:00
-- url     : https://prove2.me/submissions/6de074b2-5c54-40d7-ad22-841c66e2628e

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
    wordCount L (m + n) = ∑ u ∈ wordFinset L m, (followerFinset L u n).card := by
  classical
  unfold wordCount
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Word A => w.take m)
    (t := wordFinset L m) (by
      intro w hw
      obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
      exact mem_wordFinset.mpr ⟨hL (List.take_prefix m w).isInfix hwL,
        by simp only [List.length_take, hwlen]; omega⟩)]
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨huL, hulen⟩ := mem_wordFinset.mp hu
  apply Finset.card_bij' (fun w _ => w.drop m) (fun v _ => u ++ v)
  · intro w hw
    obtain ⟨hw, htake⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
    apply mem_followerFinset.mpr
    refine ⟨hL (List.drop_suffix m w).isInfix hwL, ?_, ?_⟩
    · simp only [List.length_drop, hwlen]
      omega
    · simpa only [← htake, List.take_append_drop] using hwL
  · intro v hv
    obtain ⟨hvL, hvlen, huvL⟩ := mem_followerFinset.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨mem_wordFinset.mpr ⟨huvL, ?_⟩, ?_⟩
    · simp only [List.length_append, hulen, hvlen]
    · simpa only [← hulen] using List.take_left (l₁ := u) (l₂ := v)
  · intro w hw
    obtain ⟨_, htake⟩ := Finset.mem_filter.mp hw
    simpa only [← htake] using List.take_append_drop m w
  · intro v hv
    simpa only [← hulen] using List.drop_left (l₁ := u) (l₂ := v)
end BalanceSpecification
