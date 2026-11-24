-- Prove2me | solution 1 for BalanceSpecification.sGap_bounded_gaps_of_leftBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:30.380806+00:00
-- url     : https://prove2.me/submissions/f02b966d-fc35-4250-b488-81f9052adf58

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_sGap_bounded_gaps_of_rightBalanced
public import Theorems.Thm_BalanceSpecification_reverseLanguage_sGapShift
public import Theorems.Thm_BalanceSpecification_rightBalanced_reverseLanguage_of_leftBalanced


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) (hL : LeftBalanced (language (sGapShift S))) :
    HasBoundedSuccessiveGaps S := by
  apply sGap_bounded_gaps_of_rightBalanced hS
  have hR := rightBalanced_reverseLanguage_of_leftBalanced hL
  rw [reverseLanguage_sGapShift hS] at hR
  exact hR
end BalanceSpecification
