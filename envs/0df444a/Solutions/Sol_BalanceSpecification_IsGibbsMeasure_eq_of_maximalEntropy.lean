-- Prove2me | solution 1 for BalanceSpecification.IsGibbsMeasure.eq_of_maximalEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:18.581514+00:00
-- url     : https://prove2.me/submissions/6bcd4e96-42b1-4453-a12a-8423e374a28c

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Definitions.Def_BalanceSpecificaton_AbsoluteContinuity
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Mathlib.Dynamics.Ergodic.Extreme
public import Definitions.Def_BalanceSpecificaton_IntrinsicErgodicity
public import Theorems.Thm_BalanceSpecification_block_divergence_le_log_of_maximalEntropy
public import Theorems.Thm_BalanceSpecification_IsGibbsMeasure_ergodic
public import Theorems.Thm_BalanceSpecification_absolutelyContinuous_of_uniform_block_divergence_bound


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
namespace IsGibbsMeasure
theorem _root_.solution {hX : X.carrier.Nonempty}
    {μ ν : ProbabilityMeasure X.carrier} (hG : IsGibbsMeasure hX μ)
    (hirr : Irreducible X) (hν : IsMaximalEntropyMeasure hX ν) : ν = μ := by
  obtain ⟨K, hB⟩ := hG.2
  have hInv := hν.choose
  have hAC : (ν : Measure X.carrier) ≪ (μ : Measure X.carrier) :=
    absolutelyContinuous_of_uniform_block_divergence_bound hG hInv
      (fun n => block_divergence_le_log_of_maximalEntropy hB hν (2 * n + 1))
  apply ProbabilityMeasure.toMeasure_injective
  exact (hG.ergodic hirr).eq_of_absolutelyContinuous
    (ν := (ν : Measure X.carrier)) hInv hAC
end IsGibbsMeasure
end BalanceSpecification
