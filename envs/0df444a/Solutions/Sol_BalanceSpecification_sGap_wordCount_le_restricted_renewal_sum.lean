-- Prove2me | solution 1 for BalanceSpecification.sGap_wordCount_le_restricted_renewal_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:44.198592+00:00
-- url     : https://prove2.me/submissions/86d7fbeb-32c8-4407-b272-e4b838fb8b37

module
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBSM
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_renewalFinset
public import Theorems.Thm_BalanceSpecification_mem_renewalGaps
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_renewalCount_zero
public import Theorems.Thm_BalanceSpecification_sGapListConcat_cons
public import Theorems.Thm_BalanceSpecification_sGapListConcat_nil
public import Theorems.Thm_BalanceSpecification_sGap_language_decomposition
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_renewalFinset
attribute [local simp] BalanceSpecification.mem_renewalGaps
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.renewalCount_zero
attribute [local simp] BalanceSpecification.sGapListConcat_cons
attribute [local simp] BalanceSpecification.sGapListConcat_nil
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter Set
open scoped Topology
namespace BalanceSpecification
theorem _root_.solution
    [TopologicalSpace Bool] [DiscreteTopology Bool] {S : Set ℕ} (hS : S.Nonempty) (n : ℕ) :
    wordCount (language (sGapShift S)) n ≤
      1 + ∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
        if a + m + 1 ≤ n then renewalCount S (n - a - m - 1) else 0 := by
  classical
  let pieces : ℕ → ℕ → Finset (Word Bool) := fun a m =>
    if a + m + 1 ≤ n then
      (renewalFinset S (n - a - m - 1)).image
        (fun v => List.replicate a false ++ v ++ true :: List.replicate m false)
    else ∅
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
      refine ⟨m, Finset.mem_range.mpr (by omega), ?_⟩
      simp only [pieces, if_pos (show a + m + 1 ≤ n by omega)]
      exact Finset.mem_image.mpr ⟨v, mem_renewalFinset.mpr ⟨hv, by omega⟩, heq.symm⟩
  have hpiece (a m : ℕ) : (pieces a m).card ≤
      if a + m + 1 ≤ n then renewalCount S (n - a - m - 1) else 0 := by
    by_cases ham : a + m + 1 ≤ n
    · simp only [pieces, if_pos ham]
      exact Finset.card_image_le
    · simp only [pieces, if_neg ham, Finset.card_empty, le_refl]
  calc
    wordCount (language (sGapShift S)) n ≤
        ({List.replicate n false} ∪ (Finset.range (n + 1)).biUnion
          (fun a => (Finset.range (n + 1)).biUnion (pieces a))).card :=
      Finset.card_le_card hsubset
    _ ≤ ({List.replicate n false} : Finset (Word Bool)).card +
        ((Finset.range (n + 1)).biUnion
          (fun a => (Finset.range (n + 1)).biUnion (pieces a))).card := Finset.card_union_le _ _
    _ ≤ 1 + ∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
        if a + m + 1 ≤ n then renewalCount S (n - a - m - 1) else 0 := by
      rw [Finset.card_singleton]
      apply Nat.add_le_add_left
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun a ha =>
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun m hm => hpiece a m))
end BalanceSpecification
