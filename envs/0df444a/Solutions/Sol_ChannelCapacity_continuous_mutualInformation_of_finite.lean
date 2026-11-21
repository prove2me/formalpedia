-- Prove2me | solution 1 for ChannelCapacity.continuous_mutualInformation_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:48:06.906676+00:00
-- url     : https://prove2.me/submissions/a6a5c602-9b0a-43b1-9eb6-bf2a070364fb

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy
public import Theorems.Thm_ChannelCapacity_continuous_outputEntropy
public import Theorems.Thm_ChannelCapacity_continuous_conditionalEntropy

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
variable [TopologicalSpace α] [TopologicalSpace β]
  [DiscreteTopology α] [DiscreteTopology β]
  [BorelSpace α] [BorelSpace β]
  [CompactSpace α] [CompactSpace β]
omit [Fintype α] [Fintype β] [TopologicalSpace β] [DiscreteTopology β] [BorelSpace β]
  [CompactSpace β]
namespace ChannelCapacity
theorem _root_.solution [Finite α] [Finite β]
    (k : Kernel α β) [IsMarkovKernel k] :
    Continuous fun p : ProbabilityMeasure α => mutualInformation p k := by
  let _instFintypeα : Fintype α := Fintype.ofFinite α
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  convert (continuous_outputEntropy k).sub (continuous_conditionalEntropy k) using 1
  ext p
  exact mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy k p
end ChannelCapacity
