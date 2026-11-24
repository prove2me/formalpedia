-- Prove2me | solution 1 for BalanceSpecification.language_codedShift_infix_generatedWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:05.136038+00:00
-- url     : https://prove2.me/submissions/660bc89d-74aa-4cb0-ac2b-3e4269e8b619

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Theorems.Thm_BalanceSpecification_IsConcatenation_block_infix_generatedWords
public import Theorems.Thm_BalanceSpecification_getElem_block
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
theorem _root_.solution
    [TopologicalSpace A] [DiscreteTopology A] {C : Set (Word A)}
    {w : Word A} (hw : w ∈ language (codedShift C)) :
    ∃ v ∈ generatedWords C, w <:+: v := by
  obtain ⟨x, hx, k, hk⟩ := hw
  obtain ⟨y, hyword, hyconcat⟩ := mem_closure_iff.mp hx
    (wordCylinder w k) (isOpen_wordCylinder w k) hk
  obtain ⟨v, hv, hinfix⟩ := IsConcatenation.block_infix_generatedWords hyconcat k w.length
  change block y k w.length = w at hyword
  exact ⟨v, hv, by simpa only [hyword] using hinfix⟩
end BalanceSpecification
