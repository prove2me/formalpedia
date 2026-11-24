-- Prove2me | solution 1 for BalanceSpecification.follower_card_reverseLanguage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:00.008741+00:00
-- url     : https://prove2.me/submissions/9174a047-16b5-4055-84d2-29e9dadbd6e1

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
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


attribute [local simp] BalanceSpecification.wordCount_reverseLanguage

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution (L : Set (Word A)) (u : Word A) (n : ℕ) :
    (followerFinset (reverseLanguage L) u n).card =
      (predecessorFinset L u.reverse n).card := by
  classical
  refine Finset.card_bij' (fun w _ => w.reverse) (fun w _ => w.reverse) ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨hwL, hwlen, huwL⟩ := mem_followerFinset.mp hw
    apply mem_predecessorFinset.mpr
    exact ⟨hwL, by simpa only [List.length_reverse] using hwlen,
      by simpa only [reverseLanguage, Set.mem_ofPred_eq, List.reverse_append] using huwL⟩
  · intro w hw
    obtain ⟨hwL, hwlen, hwuL⟩ := mem_predecessorFinset.mp hw
    apply mem_followerFinset.mpr
    exact ⟨by simpa only [reverseLanguage, Set.mem_ofPred_eq, List.reverse_reverse] using hwL,
      by simpa only [List.length_reverse] using hwlen,
      by simpa only [reverseLanguage, Set.mem_ofPred_eq, List.reverse_append,
        List.reverse_reverse] using hwuL⟩
  · intro w hw
    exact List.reverse_reverse w
  · intro w hw
    exact List.reverse_reverse w
end BalanceSpecification
