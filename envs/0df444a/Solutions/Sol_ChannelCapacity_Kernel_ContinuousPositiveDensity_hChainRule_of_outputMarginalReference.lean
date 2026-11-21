-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.hChainRule_of_outputMarginalReference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:17.95818+00:00
-- url     : https://prove2.me/submissions/bf317282-69c7-4996-8aa9-7031ff2f195e

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_klDiv_mutualInformation_chain
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
open scoped ENNReal
open ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [TopologicalSpace α] [TopologicalSpace β]
open ChannelCapacity.Kernel
open ChannelCapacity.Kernel.ContinuousPositiveDensity
variable {k : Kernel α β} [IsMarkovKernel k] [OpensMeasurableSpace α] {ν : Measure β}
variable [CompactSpace α] [CompactSpace β] [PolishSpace α] [PolishSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace β] [IsFiniteMeasure ν]
omit [TopologicalSpace β] [CompactSpace α] [CompactSpace β] [PolishSpace β] [BorelSpace β]
  [OpensMeasurableSpace α] [OpensMeasurableSpace β] [IsFiniteMeasure ν]
namespace ChannelCapacity.Kernel.ContinuousPositiveDensity
theorem _root_.solution
    (p : ProbabilityMeasure α) (ν' : Measure β)
    (hRef : Kernel.OutputMarginalReference k p ν') :
    InformationTheory.klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const _ ν') =
      InformationTheory.klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure +
        InformationTheory.klDiv (outputPrior k p).toMeasure ν' := by
  rcases hRef with ⟨q, -, rfl⟩
  let : Nonempty α := p.nonempty
  simpa using
    klDiv_mutualInformation_chain (k := k) (p := p) (ν := (outputPrior k q).toMeasure)
end ChannelCapacity.Kernel.ContinuousPositiveDensity
