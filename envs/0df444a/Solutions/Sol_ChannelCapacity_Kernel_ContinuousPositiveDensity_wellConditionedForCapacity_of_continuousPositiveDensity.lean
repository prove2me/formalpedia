-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.wellConditionedForCapacity_of_continuousPositiveDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:29.020114+00:00
-- url     : https://prove2.me/submissions/fc50efb5-9551-4f2e-8c52-07e781c87adf

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_ae_row_absolutelyContinuous_outputPrior
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_hFiniteRefKL_of_continuousPositiveDensity
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_hChainRule_of_outputMarginalReference

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
namespace ChannelCapacity.Kernel.ContinuousPositiveDensity
theorem _root_.solution
    (h : ContinuousPositiveDensity k ν) :
    Kernel.WellConditionedForCapacity k := by
  refine
    { hRowAC := h.ae_row_absolutelyContinuous_outputPrior
      hFiniteRefKL := h.hFiniteRefKL_of_continuousPositiveDensity
      hChainRule := hChainRule_of_outputMarginalReference (k := k) }
end ChannelCapacity.Kernel.ContinuousPositiveDensity
