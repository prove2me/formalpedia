-- Prove2me | solution 1 for BalanceSpecification.wordCount_unrestrictedShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:21.178252+00:00
-- url     : https://prove2.me/submissions/1b8c4a8e-d18c-40aa-8557-2de9a52818cf

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Theorems.Thm_BalanceSpecification_language_unrestrictedShift
public import Theorems.Thm_BalanceSpecification_card_allWords
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
open Filter
open scoped Topology
variable {A B : Type*}
namespace BalanceSpecification
theorem _root_.solution [Fintype A] [TopologicalSpace A] [Nonempty A] (n : ℕ) :
    wordCount (language (unrestrictedShift A)) n = (Fintype.card A) ^ n := by
  classical
  have hfin : wordFinset (language (unrestrictedShift A)) n = allWords n := by
    ext w
    simp only [mem_wordFinset, language_unrestrictedShift, Set.mem_univ, true_and, mem_allWords]
  rw [wordCount, hfin, card_allWords]
end BalanceSpecification
