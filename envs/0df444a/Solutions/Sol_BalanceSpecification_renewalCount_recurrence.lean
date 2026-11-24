-- Prove2me | solution 1 for BalanceSpecification.renewalCount_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:57.703801+00:00
-- url     : https://prove2.me/submissions/ae61547c-3d6a-47b9-ab42-4a08d6b7a2af

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Theorems.Thm_BalanceSpecification_first_sGap_generator_unique
public import Theorems.Thm_BalanceSpecification_generated_sGap_nil_or_marker
public import Theorems.Thm_BalanceSpecification_mem_renewalFinset
public import Theorems.Thm_BalanceSpecification_card_renewalPiece
public import Theorems.Thm_BalanceSpecification_renewalFinset_eq_biUnion
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


attribute [local simp] BalanceSpecification.mem_renewalFinset

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution (S : Set ℕ) {n : ℕ} (hn : 0 < n) :
    renewalCount S n = ∑ s ∈ renewalGaps S n, renewalCount S (n - s - 1) := by
  classical
  unfold renewalCount
  rw [renewalFinset_eq_biUnion S hn]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro s hs
    exact card_renewalPiece S n s
  · intro s hs t ht hst
    apply Finset.disjoint_left.mpr
    intro w hws hwt
    obtain ⟨u, hu, hequ⟩ := Finset.mem_image.mp hws
    obtain ⟨v, hv, heqv⟩ := Finset.mem_image.mp hwt
    have heq : (true :: List.replicate s false) ++ u =
        (true :: List.replicate t false) ++ v := hequ.trans heqv.symm
    have huniq := first_sGap_generator_unique
      (generated_sGap_nil_or_marker (mem_renewalFinset.mp hu).1)
      (generated_sGap_nil_or_marker (mem_renewalFinset.mp hv).1) heq
    exact hst huniq.1
end BalanceSpecification
