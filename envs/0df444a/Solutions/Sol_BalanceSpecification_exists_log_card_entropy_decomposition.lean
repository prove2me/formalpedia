-- Prove2me | solution 1 for BalanceSpecification.exists_log_card_entropy_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:32.473096+00:00
-- url     : https://prove2.me/submissions/fdbc7148-9295-4310-b915-daf6fd357033

module
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyModel
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
namespace BalanceSpecification
theorem _root_.solution {h : ℝ} (hh : 0 ≤ h) :
    ∃ n : ℕ, 1 ≤ n ∧ 0 ≤ h - Real.log n ∧ h - Real.log n < Real.log 2 := by
  let n := ⌊Real.exp h⌋₊
  have hexp : (1 : ℝ) ≤ Real.exp h := Real.one_le_exp_iff.mpr hh
  have hn : 1 ≤ n := (Nat.le_floor_iff (Real.exp_pos h).le).mpr (by simpa only [Nat.cast_one] using hexp)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hfloor : (n : ℝ) ≤ Real.exp h := Nat.floor_le (Real.exp_pos h).le
  have hnext : Real.exp h < (n : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp h)
  have hlog : Real.log n ≤ h := by
    simpa only [Real.log_exp] using Real.log_le_log hnpos hfloor
  have hdouble : Real.exp h < 2 * (n : ℝ) := hnext.trans_le (by linarith only [hnR])
  have hlt := Real.log_lt_log (Real.exp_pos h) hdouble
  rw [Real.log_exp, Real.log_mul (by norm_num) hnpos.ne'] at hlt
  exact ⟨n, hn, by linarith only [hlog], by linarith only [hlt]⟩
end BalanceSpecification
