-- Prove2me | solution 1 for BalanceSpecification.renewalFinset_eq_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:49.973949+00:00
-- url     : https://prove2.me/submissions/c20baf5d-43ff-4936-9f5d-6de6323686e2

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Theorems.Thm_BalanceSpecification_sGapListConcat_nil
public import Theorems.Thm_BalanceSpecification_sGapListConcat_cons
public import Theorems.Thm_BalanceSpecification_mem_renewalFinset
public import Theorems.Thm_BalanceSpecification_renewalCount_zero
public import Theorems.Thm_BalanceSpecification_mem_renewalGaps
public import Theorems.Thm_BalanceSpecification_append_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_generatedWords_of_mem
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


attribute [local simp] BalanceSpecification.sGapListConcat_nil
attribute [local simp] BalanceSpecification.sGapListConcat_cons
attribute [local simp] BalanceSpecification.mem_renewalFinset
attribute [local simp] BalanceSpecification.renewalCount_zero
attribute [local simp] BalanceSpecification.mem_renewalGaps

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution (S : Set ℕ) {n : ℕ} (hn : 0 < n) :
    renewalFinset S n = (renewalGaps S n).biUnion (renewalPiece S n) := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨⟨ws, hws, rfl⟩, hlen⟩ := mem_renewalFinset.mp hw
    cases ws with
    | nil => simp only [List.flatten_nil, List.length_nil] at hlen; omega
    | cons c cs =>
      obtain ⟨s, hs, rfl⟩ := hws c List.mem_cons_self
      have htail : cs.flatten ∈ generatedWords (sGapCode S) :=
        ⟨cs, fun v hv => hws v (List.mem_cons_of_mem _ hv), rfl⟩
      have hlen' : s + 1 + cs.flatten.length = n := by
        simpa only [List.flatten_cons, List.length_append, List.length_cons,
          List.length_replicate, Nat.add_comm s 1] using hlen
      apply Finset.mem_biUnion.mpr
      refine ⟨s, mem_renewalGaps.mpr ⟨by omega, hs⟩, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨cs.flatten, mem_renewalFinset.mpr ⟨htail, by omega⟩, rfl⟩
  · intro hw
    obtain ⟨s, hs, hpiece⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨hsn', hs⟩ := mem_renewalGaps.mp hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hpiece
    obtain ⟨hvgen, hvlen⟩ := mem_renewalFinset.mp hv
    apply mem_renewalFinset.mpr
    refine ⟨append_mem_generatedWords (mem_generatedWords_of_mem ⟨s, hs, rfl⟩) hvgen, ?_⟩
    simp only [List.length_append, List.length_cons, List.length_replicate, hvlen]
    omega
end BalanceSpecification
