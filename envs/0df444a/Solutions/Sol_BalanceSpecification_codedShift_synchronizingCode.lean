-- Prove2me | solution 1 for BalanceSpecification.codedShift_synchronizingCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:10.062364+00:00
-- url     : https://prove2.me/submissions/0ea35231-3997-4a5e-9aec-6ddc71aa8038

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SynchronizedCoded
public import Theorems.Thm_BalanceSpecification_generated_synchronizingCode_mem_language
public import Theorems.Thm_BalanceSpecification_exists_synchronizingCode_superword
public import Theorems.Thm_BalanceSpecification_carrier_subset_of_language_subset
public import Theorems.Thm_BalanceSpecification_language_codedShift_infix_generatedWords
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_mem_generatedWords_of_mem
public import Theorems.Thm_BalanceSpecification_mem_language_codedShift_of_mem_generatedWords


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution {v : Word A}
    (hirr : Irreducible X) (hv : IsSynchronizing (language X) v) :
    (codedShift (synchronizingCode X v)).carrier = X.carrier := by
  apply Set.Subset.antisymm
  · apply carrier_subset_of_language_subset
    intro u hu
    obtain ⟨w, hw, huw⟩ := language_codedShift_infix_generatedWords hu
    exact language_factorial X huw (generated_synchronizingCode_mem_language hv hw)
  · have hpos : ∃ w ∈ synchronizingCode X v, 0 < w.length := by
      obtain ⟨w, hw, _⟩ := exists_synchronizingCode_superword hirr hv hv.1
      exact ⟨w, hw, List.length_pos_iff.mpr hw.1⟩
    apply carrier_subset_of_language_subset
    intro u hu
    obtain ⟨w, hw, huw⟩ := exists_synchronizingCode_superword hirr hv hu
    apply (language_factorial (codedShift (synchronizingCode X v))) huw
    exact mem_language_codedShift_of_mem_generatedWords hpos (mem_generatedWords_of_mem hw)
end BalanceSpecification
