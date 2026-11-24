-- Prove2me | solution 1 for BalanceSpecification.codedShift_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:39.086299+00:00
-- url     : https://prove2.me/submissions/7201678f-82ad-4cfa-8ed3-4478f8e329dc

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Theorems.Thm_BalanceSpecification_language_codedShift_infix_generatedWords
public import Theorems.Thm_BalanceSpecification_mem_language_codedShift_iff
public import Theorems.Thm_BalanceSpecification_exists_nonempty_generator_of_codedShift_nonempty
public import Theorems.Thm_BalanceSpecification_append_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace A] [DiscreteTopology A]
    (C : Set (Word A)) : Irreducible (codedShift C) := by
  intro u hu v hv
  have hnonempty : (codedShift C).carrier.Nonempty := by
    obtain ⟨x, hx, _, _⟩ := hu
    exact ⟨x, hx⟩
  have hC := exists_nonempty_generator_of_codedShift_nonempty hnonempty
  obtain ⟨U, hU, ⟨p, q, rfl⟩⟩ := language_codedShift_infix_generatedWords hu
  obtain ⟨V, hV, ⟨r, s, rfl⟩⟩ := language_codedShift_infix_generatedWords hv
  have hfull : u ++ (q ++ r) ++ v ∈ language (codedShift C) := by
    apply (mem_language_codedShift_iff hC).mpr
    refine ⟨(p ++ u ++ q) ++ (r ++ v ++ s), append_mem_generatedWords hU hV, p, s, ?_⟩
    simp only [List.append_assoc]
  refine ⟨q ++ r, ?_, hfull⟩
  apply language_factorial (codedShift C) (u := q ++ r)
    (v := u ++ (q ++ r) ++ v) _ hfull
  exact ⟨u, v, rfl⟩
end BalanceSpecification
