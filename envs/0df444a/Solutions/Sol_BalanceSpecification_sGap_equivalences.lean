-- Prove2me | solution 1 for BalanceSpecification.sGap_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:19.922663+00:00
-- url     : https://prove2.me/submissions/1135b0ce-ea82-4f43-b47a-b382ab26b12c

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_sGapShift_nonempty
public import Theorems.Thm_BalanceSpecification_sGap_hasVariableSpecification_of_bounded_gaps
public import Theorems.Thm_BalanceSpecification_sGap_bounded_gaps_of_rightBalanced
public import Theorems.Thm_BalanceSpecification_sGap_bounded_gaps_of_leftBalanced
public import Theorems.Thm_BalanceSpecification_biBalanced_of_hasVariableSpecification
public import Theorems.Thm_BalanceSpecification_rightBalanced_of_hasVariableSpecification


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) :
    (HasBoundedSuccessiveGaps S ↔ HasVariableSpecification (sGapShift S)) ∧
    (HasBoundedSuccessiveGaps S ↔ BiBalanced (language (sGapShift S))) ∧
    (HasBoundedSuccessiveGaps S ↔
      RightBalanced (language (sGapShift S)) ∨ LeftBalanced (language (sGapShift S))) := by
  have hspec := sGap_hasVariableSpecification_of_bounded_gaps hS
  have hbi : HasBoundedSuccessiveGaps S → BiBalanced (language (sGapShift S)) :=
    fun h => biBalanced_of_hasVariableSpecification (sGapShift_nonempty hS) (hspec h)
  refine ⟨⟨hspec, ?_⟩, ⟨hbi, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    exact sGap_bounded_gaps_of_rightBalanced hS
      (rightBalanced_of_hasVariableSpecification (sGapShift_nonempty hS) h)
  · exact fun h => sGap_bounded_gaps_of_rightBalanced hS h.1
  · exact fun h => Or.inl (hbi h).1
  · intro h
    exact h.elim (sGap_bounded_gaps_of_rightBalanced hS) (sGap_bounded_gaps_of_leftBalanced hS)
end BalanceSpecification
