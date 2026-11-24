-- Prove2me | solution 1 for BalanceSpecification.leftBalanced_of_bounded_bridges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:18:38.628364+00:00
-- url     : https://prove2.me/submissions/efb7f1bf-1709-4ca3-9843-08c7367a11c0

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Specification
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_rightBalanced_of_bounded_bridges
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


attribute [local simp] BalanceSpecification.mem_shortWords

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution (hL : IsFactorial L)
    (hpos : ∀ n, 0 < wordCount L n) {N : ℕ}
    (hbridge : ∀ u ∈ L, ∀ v ∈ L,
      ∃ w : Word A, w.length ≤ N ∧ u ++ w ++ v ∈ L) : LeftBalanced L := by
  have hrev : RightBalanced (reverseLanguage L) := by
    apply rightBalanced_of_bounded_bridges hL.reverseLanguage
      (fun n => by simpa only [wordCount_reverseLanguage] using hpos n) (N := N)
    intro u hu v hv
    obtain ⟨w, hwN, hvwu⟩ := hbridge v.reverse hv u.reverse hu
    refine ⟨w.reverse, ?_, ?_⟩
    · simpa only [List.length_reverse] using hwN
    · simpa only [reverseLanguage, Set.mem_ofPred_eq, List.reverse_append,
        List.reverse_reverse, List.append_assoc] using hvwu
  obtain ⟨c, hc, hbound⟩ := hrev
  refine ⟨c, hc, ?_⟩
  intro u hu n hn
  have hu' : u.reverse ∈ reverseLanguage L := by
    simpa only [reverseLanguage, Set.mem_ofPred_eq, List.reverse_reverse] using hu
  simpa only [follower_card_reverseLanguage, List.reverse_reverse,
    wordCount_reverseLanguage] using hbound u.reverse hu' n hn
end BalanceSpecification
