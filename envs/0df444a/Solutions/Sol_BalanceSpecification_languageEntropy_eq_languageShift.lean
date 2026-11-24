-- Prove2me | solution 1 for BalanceSpecification.languageEntropy_eq_languageShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:25.363799+00:00
-- url     : https://prove2.me/submissions/c01d0037-e010-497c-b92b-11ad9062fcc3

module
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Theorems.Thm_BalanceSpecification_mem_languageShift_iff
public import Theorems.Thm_BalanceSpecification_nonempty_languageShift_of_words_all_lengths
public import Theorems.Thm_BalanceSpecification_languageShift_empty_of_missing_length
public import Theorems.Thm_BalanceSpecification_languageEntropy_eq_rate
public import Theorems.Thm_BalanceSpecification_languageEntropy_eq_bot_of_missing_length
public import Theorems.Thm_BalanceSpecification_rate_languageShift_eq
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


attribute [local simp] BalanceSpecification.mem_languageShift_iff

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {L : Set (Word A)} (hL : IsFactorial L) :
    languageEntropy L = languageEntropy (language (languageShift L)) := by
  classical
  by_cases hpos : ∀ n, 0 < wordCount L n
  · have hA : Nonempty A := by
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (hpos 1)
      have hlen := (mem_wordFinset.mp hw).2
      cases w with
      | nil => simp only [List.length_nil, Nat.zero_ne_one] at hlen
      | cons a l => exact ⟨a⟩
    let : Nonempty A := hA
    have hcore : (languageShift L).carrier.Nonempty :=
      nonempty_languageShift_of_words_all_lengths hL (by
        intro n
        obtain ⟨w, hw⟩ := Finset.card_pos.mp (hpos n)
        exact ⟨w, (mem_wordFinset.mp hw).1, (mem_wordFinset.mp hw).2⟩)
    rw [languageEntropy_eq_rate hL hpos,
      languageEntropy_eq_rate (language_factorial (languageShift L))
        (wordCount_pos_of_nonempty hcore), rate_languageShift_eq hL hpos]
  · obtain ⟨n, hn⟩ := not_forall.mp hpos
    have hnzero : wordCount L n = 0 := Nat.eq_zero_of_not_pos hn
    have hcoreempty := languageShift_empty_of_missing_length hnzero
    have hcorezero : wordCount (language (languageShift L)) 0 = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨⟨x, hx, _, _⟩, _⟩ := mem_wordFinset.mp hw
      simp only [hcoreempty, Set.notMem_empty] at hx
    rw [languageEntropy_eq_bot_of_missing_length hL hnzero,
      languageEntropy_eq_bot_of_missing_length (language_factorial (languageShift L)) hcorezero]
end BalanceSpecification
