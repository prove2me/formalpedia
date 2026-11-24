-- Prove2me | solution 1 for BalanceSpecification.sGapPeriodic_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:39.699591+00:00
-- url     : https://prove2.me/submissions/c0ad4e59-1fb6-4f06-ae6d-8e70ac1c2198

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_sGapPeriodic_return
public import Theorems.Thm_BalanceSpecification_sGapPeriodic_before_return

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution : Function.Injective sGapPeriodic := by
  intro s t heq
  by_contra hne
  obtain hst | hts := lt_or_gt_of_ne hne
  · have h := congrFun heq ((s + 1 : ℕ) : ℤ)
    rw [sGapPeriodic_return, sGapPeriodic_before_return t s hst] at h
    cases h
  · have h := congrFun heq ((t + 1 : ℕ) : ℤ)
    rw [sGapPeriodic_return, sGapPeriodic_before_return s t hts] at h
    cases h
end BalanceSpecification
