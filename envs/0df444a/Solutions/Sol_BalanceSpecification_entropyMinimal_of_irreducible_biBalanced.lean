-- Prove2me | solution 1 for BalanceSpecification.entropyMinimal_of_irreducible_biBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:19.56804+00:00
-- url     : https://prove2.me/submissions/6744c987-60a2-44d2-895f-67e00e081629

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Definitions.Def_BalanceSpecificaton_MainEquivalence
public import Theorems.Thm_BalanceSpecification_IsGibbsMeasure_ergodic
public import Theorems.Thm_BalanceSpecification_entropyMinimal_of_ergodic_gibbs
public import Theorems.Thm_BalanceSpecification_exists_invariantGibbs_of_biBalanced


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Nonempty)
    (hirr : Irreducible X) (hB : BiBalanced (language X)) : EntropyMinimal X := by
  obtain ⟨μ, hG⟩ := exists_invariantGibbs_of_biBalanced hX hB
  exact entropyMinimal_of_ergodic_gibbs hX hG (hG.ergodic hirr)
end BalanceSpecification
