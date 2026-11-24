-- Prove2me | solution 1 for BalanceSpecification.exists_binary_specification_shift_of_entropy_lt_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:27.091775+00:00
-- url     : https://prove2.me/submissions/2755d1e8-3eed-44b4-837c-2b79178b562c

module
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyModel
public import Theorems.Thm_BalanceSpecification_exists_sGap_specification_with_pressure
public import Theorems.Thm_BalanceSpecification_entropy_constantShift
public import Theorems.Thm_BalanceSpecification_hasSpecification_constantShift
public import Theorems.Thm_BalanceSpecification_sGapShift_nonempty
public import Theorems.Thm_BalanceSpecification_sGap_entropy_eq_log_of_tsum_pressure


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    {h : ℝ} (hh : 0 ≤ h) (hsmall : h < Real.log 2) :
    ∃ Y : ShiftSpace Bool, ∃ hY : Y.carrier.Nonempty,
      HasSpecification Y ∧ entropy Y hY = h := by
  by_cases hzero : h = 0
  · refine ⟨constantShift true, constantShift_nonempty true, hasSpecification_constantShift true, ?_⟩
    rw [entropy_constantShift, hzero]
  · have hpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hzero)
    obtain ⟨S, h0, _, hpressure, hspec⟩ := exists_sGap_specification_with_pressure hpos hsmall
    have hS : S.Nonempty := ⟨0, h0⟩
    refine ⟨sGapShift S, sGapShift_nonempty hS, hspec, ?_⟩
    rw [sGap_entropy_eq_log_of_tsum_pressure hS (Real.one_lt_exp_iff.mpr hpos) hpressure,
      Real.log_exp]
end BalanceSpecification
