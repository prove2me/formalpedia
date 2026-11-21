-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.isCompact_univ_probabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:41.75433+00:00
-- url     : https://prove2.me/submissions/4b2b133a-5456-4746-95ba-9d3d6bc5b084

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
variable [CompactSpace α] [PolishSpace α] [BorelSpace α] [Nonempty α]
omit [Nonempty α]
namespace ChannelCapacity.Kernel.ContinuousPositiveDensity
theorem _root_.solution :
    IsCompact (Set.univ : Set (ProbabilityMeasure α)) :=
  isCompact_univ
end ChannelCapacity.Kernel.ContinuousPositiveDensity
