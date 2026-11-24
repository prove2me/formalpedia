-- Prove2me | solution 1 for BalanceSpecification.rightBalanced_of_bounded_bridges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:51.256797+00:00
-- url     : https://prove2.me/submissions/1b9f0222-7e40-4520-b091-0754fddad03a

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Specification
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_shortWords_card_pos
public import Theorems.Thm_BalanceSpecification_wordCount_le_follower_mul_shortWords
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
      ∃ w : Word A, w.length ≤ N ∧ u ++ w ++ v ∈ L) : RightBalanced L := by
  have hshort : (0 : ℝ) < (shortWords (A := A) N).card := by
    exact_mod_cast shortWords_card_pos (A := A) N
  refine ⟨1 / (shortWords (A := A) N).card, div_pos zero_lt_one hshort, ?_⟩
  intro u hu n _
  have hn : (0 : ℝ) < wordCount L n := by exact_mod_cast hpos n
  have hcard := wordCount_le_follower_mul_shortWords hL (hbridge u hu) n
  have hcard' : (wordCount L n : ℝ) ≤
      ((followerFinset L u n).card : ℝ) * (shortWords (A := A) N).card := by
    exact_mod_cast hcard
  apply (div_le_div_iff₀ hshort hn).mpr
  simpa only [one_mul] using hcard'
end BalanceSpecification
