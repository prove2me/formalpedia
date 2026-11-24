-- Prove2me | solution 1 for BalanceSpecification.mem_generatedWords_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:35:13.52568+00:00
-- url     : https://prove2.me/submissions/64f83710-8816-40fb-aee1-93e5f771305d

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Topology.Continuous
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Coded
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block


attribute [local simp] BalanceSpecification.nil_mem_generatedWords

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution {C : Set (Word A)} {w : Word A} (hw : w ∈ C) :
    w ∈ generatedWords C := by
  refine ⟨[w], ?_, by simp only [List.flatten_cons, List.flatten_nil, List.append_nil]⟩
  intro v hv
  exact (List.mem_singleton.mp hv) ▸ hw
end BalanceSpecification
