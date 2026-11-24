-- Prove2me | solution 1 for BalanceSpecification.sGap_language_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:46.891262+00:00
-- url     : https://prove2.me/submissions/e88d4af8-7bfd-4ded-bbd7-f01531959f0f

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Theorems.Thm_BalanceSpecification_GapRead_decompose_markers
public import Theorems.Thm_BalanceSpecification_eq_replicate_false_of_true_not_mem
public import Theorems.Thm_BalanceSpecification_mem_language_sGapShift_iff


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {w : Word Bool}
    (hw : w ∈ language (sGapShift S)) :
    w = List.replicate w.length false ∨
      ∃ a m : ℕ, ∃ v : Word Bool, v ∈ generatedWords (sGapCode S) ∧
        w = List.replicate a false ++ v ++ true :: List.replicate m false := by
  by_cases ht : true ∈ w
  · obtain ⟨a, b, _, hread⟩ := (mem_language_sGapShift_iff hS).mp hw
    obtain ⟨v, m, hv, heq⟩ := hread.decompose_markers ht
    exact Or.inr ⟨a, m, v, hv, heq⟩
  · exact Or.inl (eq_replicate_false_of_true_not_mem ht)
end BalanceSpecification
