-- Prove2me | solution 1 for BalanceSpecification.sGap_entropy_eq_log_of_tsum_pressure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:18.893576+00:00
-- url     : https://prove2.me/submissions/54bd8e10-2a8a-449d-a0de-bede6f5c2c37

module
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Theorems.Thm_BalanceSpecification_sGap_entropy_eq_log_of_pressure
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
public import Theorems.Thm_BalanceSpecification_sGapShift_nonempty
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
theorem _root_.solution [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {β : ℝ} (hβ : 1 < β)
    (hroot : (∑' s : S, (β ^ (s.val + 1))⁻¹) = 1) :
    entropy (sGapShift S) (sGapShift_nonempty hS) = Real.log β := by
  have hs : Summable (fun s : S => (β ^ (s.val + 1))⁻¹) := by
    by_contra hnot
    have hz := tsum_eq_zero_of_not_summable hnot
    rw [hroot] at hz
    exact one_ne_zero hz
  apply sGap_entropy_eq_log_of_pressure hS hβ
  simpa only [inv_pow] using (hroot ▸ hs.hasSum)
end BalanceSpecification
