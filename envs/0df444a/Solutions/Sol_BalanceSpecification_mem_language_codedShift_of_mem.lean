-- Prove2me | solution 1 for BalanceSpecification.mem_language_codedShift_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:52.8394+00:00
-- url     : https://prove2.me/submissions/28244c42-67ee-4d69-8a7a-cafa74447a22

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Theorems.Thm_BalanceSpecification_mem_language_codedShift_of_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_mem_generatedWords_of_mem


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace A]
    {C : Set (Word A)} (hC : ∃ q ∈ C, 0 < q.length)
    {w : Word A} (hw : w ∈ C) : w ∈ language (codedShift C) :=
  mem_language_codedShift_of_mem_generatedWords hC (mem_generatedWords_of_mem hw)
end BalanceSpecification
