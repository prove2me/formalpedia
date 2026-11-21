-- Prove2me | solution 1 for ChannelCapacity.continuous_outputEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:36.008627+00:00
-- url     : https://prove2.me/submissions/b301ff46-ffbb-4bda-8f90-bc6f7201d92e

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_continuous_outputPrior_toReal_apply_singleton
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_dirac
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_id
attribute [local simp] ChannelCapacity.independentJointLaw_toMeasure
attribute [local simp] ChannelCapacity.jointLaw_toMeasure
attribute [local simp] ChannelCapacity.outputPrior_toMeasure
attribute [local simp] ProbabilityMeasure.convexCombination_toMeasure



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
omit [Fintype α] [TopologicalSpace β] [DiscreteTopology β] [BorelSpace β] [CompactSpace β]
namespace ChannelCapacity
theorem _root_.solution [Finite α] (k : Kernel α β) [IsMarkovKernel k] :
    Continuous fun p : ProbabilityMeasure α => ProbabilityMeasure.entropy (outputPrior k p) := by
  let _instFintypeα : Fintype α := Fintype.ofFinite α
  simpa [ProbabilityMeasure.entropy] using
    (continuous_finsetSum (s := (Finset.univ : Finset β)) fun b _hb =>
      Real.continuous_negMulLog.comp (continuous_outputPrior_toReal_apply_singleton k b))
end ChannelCapacity
