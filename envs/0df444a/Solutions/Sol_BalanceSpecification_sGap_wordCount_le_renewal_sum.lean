-- Prove2me | solution 1 for BalanceSpecification.sGap_wordCount_le_renewal_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:33.7458+00:00
-- url     : https://prove2.me/submissions/f10205c3-fea9-4312-a0a4-fd1c5c44f9a6

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
public import Theorems.Thm_BalanceSpecification_sGap_language_decomposition
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
theorem _root_.solution [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) (n : ℕ) :
    wordCount (language (sGapShift S)) n ≤
      1 + ∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
        renewalCount S (n - a - m - 1) := by
  classical
  let pieces : ℕ → ℕ → Finset (Word Bool) := fun a m =>
    (renewalFinset S (n - a - m - 1)).image
      (fun v => List.replicate a false ++ v ++ true :: List.replicate m false)
  have hsubset : wordFinset (language (sGapShift S)) n ⊆
      {List.replicate n false} ∪
        (Finset.range (n + 1)).biUnion (fun a => (Finset.range (n + 1)).biUnion (pieces a)) := by
    intro w hw
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
    obtain hzero | ⟨a, m, v, hv, heq⟩ := sGap_language_decomposition hS hwL
    · apply Finset.mem_union_left
      exact Finset.mem_singleton.mpr (by simpa only [hwlen] using hzero)
    · apply Finset.mem_union_right
      have hlen : a + v.length + (m + 1) = n := by
        rw [heq] at hwlen
        simpa only [List.length_append, List.length_replicate, List.length_cons] using hwlen
      apply Finset.mem_biUnion.mpr
      refine ⟨a, Finset.mem_range.mpr (by omega), Finset.mem_biUnion.mpr ?_⟩
      refine ⟨m, Finset.mem_range.mpr (by omega), Finset.mem_image.mpr ?_⟩
      exact ⟨v, mem_renewalFinset.mpr ⟨hv, by omega⟩, heq.symm⟩
  have hpiece (a m : ℕ) : (pieces a m).card ≤ renewalCount S (n - a - m - 1) :=
    Finset.card_image_le
  calc
    wordCount (language (sGapShift S)) n ≤
        ({List.replicate n false} ∪
          (Finset.range (n + 1)).biUnion
            (fun a => (Finset.range (n + 1)).biUnion (pieces a))).card :=
      Finset.card_le_card hsubset
    _ ≤ ({List.replicate n false} : Finset (Word Bool)).card +
        ((Finset.range (n + 1)).biUnion
          (fun a => (Finset.range (n + 1)).biUnion (pieces a))).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + ∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
        renewalCount S (n - a - m - 1) := by
      rw [Finset.card_singleton]
      apply Nat.add_le_add_left
      calc
        ((Finset.range (n + 1)).biUnion
            (fun a => (Finset.range (n + 1)).biUnion (pieces a))).card ≤
            ∑ a ∈ Finset.range (n + 1), ((Finset.range (n + 1)).biUnion (pieces a)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
            renewalCount S (n - a - m - 1) := by
          apply Finset.sum_le_sum
          intro a ha
          exact Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun m hm => hpiece a m))
end BalanceSpecification
