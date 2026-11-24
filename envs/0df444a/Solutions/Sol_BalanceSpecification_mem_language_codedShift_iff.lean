-- Prove2me | solution 1 for BalanceSpecification.mem_language_codedShift_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:51.879787+00:00
-- url     : https://prove2.me/submissions/ead51d31-f1ed-4b12-8b18-bbf8b5cc76b8

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Theorems.Thm_BalanceSpecification_language_codedShift_infix_generatedWords
public import Theorems.Thm_BalanceSpecification_mem_language_codedShift_of_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_language_factorial


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace A] [DiscreteTopology A]
    {C : Set (Word A)} (hC : ∃ q ∈ C, 0 < q.length) {w : Word A} :
    w ∈ language (codedShift C) ↔ ∃ v ∈ generatedWords C, w <:+: v := by
  refine ⟨language_codedShift_infix_generatedWords, ?_⟩
  rintro ⟨v, hv, hwv⟩
  exact language_factorial (codedShift C) hwv
    (mem_language_codedShift_of_mem_generatedWords hC hv)
end BalanceSpecification
