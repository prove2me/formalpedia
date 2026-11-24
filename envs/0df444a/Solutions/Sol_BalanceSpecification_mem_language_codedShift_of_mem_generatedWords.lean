-- Prove2me | solution 1 for BalanceSpecification.mem_language_codedShift_of_mem_generatedWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:05.896581+00:00
-- url     : https://prove2.me/submissions/6db6ebb2-7c1f-4ab9-aa7d-8bb7b0a3b5b5

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Theorems.Thm_BalanceSpecification_exists_realization_generatedWords_at_cut
public import Theorems.Thm_BalanceSpecification_mem_codedShift_of_isConcatenation


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace A]
    {C : Set (Word A)} (hC : ∃ q ∈ C, 0 < q.length)
    {v : Word A} (hv : v ∈ generatedWords C) : v ∈ language (codedShift C) := by
  obtain ⟨x, p, hp, _, hwords, hx⟩ := exists_realization_generatedWords_at_cut hC hv
  exact ⟨x, mem_codedShift_of_isConcatenation ⟨p, hp, hwords⟩, 0, hx⟩
end BalanceSpecification
