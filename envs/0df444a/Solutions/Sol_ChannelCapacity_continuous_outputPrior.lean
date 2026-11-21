-- Prove2me | solution 1 for ChannelCapacity.continuous_outputPrior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:36.560448+00:00
-- url     : https://prove2.me/submissions/4a0b148b-95e0-4fb7-b757-1f1aea9e739b

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_ProbabilityMeasure_integral_eq_sum_singletonMass
public import Theorems.Thm_ChannelCapacity_continuous_outputPrior_toReal_apply_singleton

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
omit [Fintype α] [Fintype β] [DiscreteTopology β]
namespace ChannelCapacity
theorem _root_.solution [Finite α] [Finite β] (k : Kernel α β) [IsMarkovKernel k] :
    Continuous fun p : ProbabilityMeasure α => outputPrior k p := by
  let _instFintypeα : Fintype α := Fintype.ofFinite α
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  rw [ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral]
  intro f
  have hsum :
      Continuous fun p : ProbabilityMeasure α =>
        ∑ b, ((outputPrior k p).toMeasure {b}).toReal * f b :=
    continuous_finsetSum (s := (Finset.univ : Finset β)) fun b _hb =>
      (continuous_outputPrior_toReal_apply_singleton k b).mul continuous_const
  convert hsum using 1
  ext p
  rw [ProbabilityMeasure.integral_eq_sum_singletonMass]
end ChannelCapacity
