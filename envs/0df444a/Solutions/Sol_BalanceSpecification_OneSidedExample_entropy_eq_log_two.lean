-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.entropy_eq_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:08.682768+00:00
-- url     : https://prove2.me/submissions/a2cae77b-f2ca-4234-8c7c-bfac0fc2f6c6

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_wordCount_lower_bound
public import Theorems.Thm_BalanceSpecification_OneSidedExample_wordCount_uniform_upper_bound
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
public import Theorems.Thm_BalanceSpecification_tendsto_entropy
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
theorem _root_.solution : entropy shift nonempty = Real.log 2 := by
  have hlow : Real.log 2 ≤ entropy shift nonempty := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_entropy nonempty)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hc : (2 : ℝ) ^ n ≤ wordCount (language shift) n := by
      exact_mod_cast wordCount_lower_bound n
    have H := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) n) hc
    rw [Real.log_pow] at H
    exact (le_div_iff₀ hnpos).mpr (by simpa only [mul_comm] using H)
  have hupp : entropy shift nonempty ≤ Real.log 2 := by
    have ht : Tendsto (fun n : ℕ => Real.log 5 / (n : ℝ) + Real.log 2)
        atTop (𝓝 (Real.log 2)) := by
      simpa only [zero_add] using
        (tendsto_const_div_atTop_nhds_zero_nat (Real.log 5)).add
          (tendsto_const_nhds (x := Real.log 2))
    apply le_of_tendsto_of_tendsto (tendsto_entropy nonempty) ht
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hc : (wordCount (language shift) n : ℝ) ≤ 5 * (2 : ℝ) ^ n := by
      exact_mod_cast wordCount_uniform_upper_bound n
    have hcount : (0 : ℝ) < wordCount (language shift) n := by
      exact_mod_cast wordCount_pos_of_nonempty nonempty n
    have H := Real.log_le_log hcount hc
    rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (pow_ne_zero _ (by norm_num)),
      Real.log_pow] at H
    apply (div_le_iff₀ hnpos).mpr
    rw [add_mul, div_mul_cancel₀ _ hnpos.ne']
    simpa only [mul_comm] using H
  exact le_antisymm hupp hlow
end BalanceSpecification.OneSidedExample
