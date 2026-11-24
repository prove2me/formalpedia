-- Prove2me | solution 1 for BalanceSpecification.sGapPeriodic_before_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:52.324895+00:00
-- url     : https://prove2.me/submissions/dc8bf396-00f1-4a3e-bd41-c4ccca9de6e2

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
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



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution (s i : ℕ) (hi : i < s) :
    sGapPeriodic s (i + 1 : ℕ) = false := by
  have hmod : ((i + 1 : ℕ) : ℤ) % (s + 1 : ℕ) = (i + 1 : ℕ) :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Nat.succ_lt_succ hi)
  simp only [sGapPeriodic, periodicConfiguration, List.length_cons, List.length_replicate,
    hmod, Int.toNat_natCast, List.getElem_cons_succ, List.getElem_replicate]
end BalanceSpecification
