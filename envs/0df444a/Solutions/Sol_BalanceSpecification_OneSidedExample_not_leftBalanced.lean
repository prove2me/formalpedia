-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.not_leftBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:36.917818+00:00
-- url     : https://prove2.me/submissions/498f87bc-d2b6-4501-b293-ff199ed2ef7c

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_wordCount_lower_bound
public import Theorems.Thm_BalanceSpecification_OneSidedExample_probeWord_mem_language
public import Theorems.Thm_BalanceSpecification_OneSidedExample_predecessor_probe_card_le_one
public import Theorems.Thm_BalanceSpecification_OneSidedExample_length_runWord
public import Theorems.Thm_BalanceSpecification_OneSidedExample_nonempty
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
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.OneSidedExample.length_runWord
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



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution : ¬ LeftBalanced (language shift) := by
  rintro ⟨c₀, hc, hbound⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / c₀)
  let n := k + 1
  have hn : 1 ≤ n := by dsimp only [n]; omega
  have hpos : (0 : ℝ) < wordCount (language shift) n := by
    exact_mod_cast wordCount_pos_of_nonempty nonempty n
  have hprod := (le_div_iff₀ hpos).mp
    (hbound (probeWord n) (probeWord_mem_language n) n hn)
  have hpre : ((predecessorFinset (language shift) (probeWord n) n).card : ℝ) ≤ 1 := by
    exact_mod_cast predecessor_probe_card_le_one hn
  have hcount : (k : ℝ) ≤ wordCount (language shift) n := by
    have H : k ≤ wordCount (language shift) n :=
      (show k ≤ n by dsimp only [n]; omega).trans
        (Nat.le_of_lt Nat.lt_two_pow_self |>.trans (wordCount_lower_bound n))
    exact_mod_cast H
  have hkc : 1 < (k : ℝ) * c₀ := (div_lt_iff₀ hc).mp hk
  have hkc' : (k : ℝ) * c₀ ≤ c₀ * wordCount (language shift) n := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcount hc.le
  exact (not_le_of_gt hkc) (hkc'.trans (hprod.trans hpre))
end BalanceSpecification.OneSidedExample
