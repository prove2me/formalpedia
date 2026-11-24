-- Prove2me | solution 1 for BalanceSpecification.synchronized_biBalanced_iff_hasVariableSpecification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:20:27.656566+00:00
-- url     : https://prove2.me/submissions/8c47e2e9-095f-4c93-99a1-595a5357e611

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Definitions.Def_BalanceSpecificaton_MainEquivalence
public import Theorems.Thm_BalanceSpecification_entropyMinimal_of_irreducible_biBalanced
public import Theorems.Thm_BalanceSpecification_biBalanced_of_hasVariableSpecification
public import Theorems.Thm_BalanceSpecification_hasVariableSpecification_of_entropyMinimal_synchronized_biBalanced
public import Theorems.Thm_BalanceSpecification_synchronized_of_hasVariableSpecification


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Nonempty)
    (hirr : Irreducible X) :
    (Synchronized X ∧ BiBalanced (language X)) ↔ HasVariableSpecification X := by
  constructor
  · rintro ⟨hS, hB⟩
    exact hasVariableSpecification_of_entropyMinimal_synchronized_biBalanced
      (entropyMinimal_of_irreducible_biBalanced hX hirr hB) hS hB
  · intro hspec
    exact ⟨synchronized_of_hasVariableSpecification hX hspec,
      biBalanced_of_hasVariableSpecification hX hspec⟩
end BalanceSpecification
