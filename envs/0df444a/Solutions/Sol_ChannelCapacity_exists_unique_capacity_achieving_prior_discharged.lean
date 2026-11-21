-- Prove2me | solution 1 for ChannelCapacity.exists_unique_capacity_achieving_prior_discharged
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:48:00.057829+00:00
-- url     : https://prove2.me/submissions/e6e5c00b-6f99-4753-b40c-6438722b0608

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_upperSemicontinuous_mutualInformation
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_wellConditionedForCapacity_of_continuousPositiveDensity
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_univ_nonempty_probabilityMeasure
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_isCompact_univ_probabilityMeasure
public import Theorems.Thm_ChannelCapacity_exists_unique_capacity_achieving_prior


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
open ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [TopologicalSpace α] [TopologicalSpace β]
variable [CompactSpace α] [CompactSpace β] [PolishSpace α] [PolishSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace α] [OpensMeasurableSpace β]
variable [MeasurableSpace.CountableOrCountablyGenerated α β]
variable [Nonempty α]
namespace ChannelCapacity
theorem _root_.solution
    (k : Kernel α β) [IsMarkovKernel k]
    (ν : Measure β) [IsFiniteMeasure ν]
    (hDensity : Kernel.ContinuousPositiveDensity k ν)
    (hInj : Kernel.InjectivePriorPushforward k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k := by
  exact exists_unique_capacity_achieving_prior k hInj
    (Kernel.ContinuousPositiveDensity.wellConditionedForCapacity_of_continuousPositiveDensity
      (k := k) (ν := ν) hDensity)
    Kernel.ContinuousPositiveDensity.univ_nonempty_probabilityMeasure
    Kernel.ContinuousPositiveDensity.isCompact_univ_probabilityMeasure
    hDensity.upperSemicontinuous_mutualInformation
end ChannelCapacity
