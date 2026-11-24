-- Prove2me | solution 1 for BalanceSpecification.wordCount_constantShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:59.911477+00:00
-- url     : https://prove2.me/submissions/bc2506bd-baf7-4646-9bc5-3109d140cb7e

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Theorems.Thm_BalanceSpecification_mem_language_constantShift_iff
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
theorem _root_.solution [Fintype A] [TopologicalSpace A] [T1Space A]
    (a : A) (n : ℕ) : wordCount (language (constantShift a)) n = 1 := by
  classical
  have hfin : wordFinset (language (constantShift a)) n = {List.replicate n a} := by
    ext w
    simp only [mem_wordFinset, mem_language_constantShift_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hw, hlen⟩
      simpa only [hlen] using hw
    · intro hw
      have hlen : w.length = n := by rw [hw, List.length_replicate]
      exact ⟨by simpa only [hlen] using hw, hlen⟩
  rw [wordCount, hfin, Finset.card_singleton]
end BalanceSpecification
