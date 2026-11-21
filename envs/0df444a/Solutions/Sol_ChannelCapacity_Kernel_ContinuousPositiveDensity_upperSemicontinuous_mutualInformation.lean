-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.upperSemicontinuous_mutualInformation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:33.557167+00:00
-- url     : https://prove2.me/submissions/4127349e-3cb8-443f-81c9-58d841c9311a

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged

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
namespace ChannelCapacity.Kernel.ContinuousPositiveDensity
theorem _root_.solution
    (h : ContinuousPositiveDensity k ν) :
    UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k :=
  h.mutualInformation_usc
end ChannelCapacity.Kernel.ContinuousPositiveDensity
