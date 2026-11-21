-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.aemeasurable_outputDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:49.833256+00:00
-- url     : https://prove2.me/submissions/f4cf8f2c-f549-451e-ba96-b6304564a4d1

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
variable [CompactSpace α] [CompactSpace β] [PolishSpace α] [PolishSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace β] [IsFiniteMeasure ν]
omit [CompactSpace α] [CompactSpace β] [BorelSpace α] [BorelSpace β]
namespace ChannelCapacity.Kernel.ContinuousPositiveDensity
theorem _root_.solution (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    AEMeasurable (h.outputDensity p) ν := by
  have hbase :
      AEMeasurable
        (Function.uncurry fun a b => (h.density a b : ENNReal))
        (p.toMeasure.prod ν) := by
    exact (ENNReal.continuous_coe.comp h.continuous_density).aemeasurable
  exact hbase.lintegral_prod_left (μ := p.toMeasure) (ν := ν)
end ChannelCapacity.Kernel.ContinuousPositiveDensity
