-- Prove2me | solution 1 for BalanceSpecification.intrinsicallyErgodic_of_irreducible_biBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:20:27.097366+00:00
-- url     : https://prove2.me/submissions/47a53811-4a71-49d3-b46b-882372a3f390

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Definitions.Def_BalanceSpecificaton_AbsoluteContinuity
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Mathlib.Dynamics.Ergodic.Extreme
public import Definitions.Def_BalanceSpecificaton_IntrinsicErgodicity
public import Theorems.Thm_BalanceSpecification_IsGibbsMeasure_eq_of_maximalEntropy
public import Theorems.Thm_BalanceSpecification_IsGibbsMeasure_isMaximalEntropyMeasure
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
    (hirr : Irreducible X) (hB : BiBalanced (language X)) : IntrinsicallyErgodic X hX := by
  obtain ⟨μ, hG⟩ := exists_invariantGibbs_of_biBalanced hX hB
  exact ⟨μ, hG.isMaximalEntropyMeasure, fun ν hν => hG.eq_of_maximalEntropy hirr hν⟩
end BalanceSpecification
