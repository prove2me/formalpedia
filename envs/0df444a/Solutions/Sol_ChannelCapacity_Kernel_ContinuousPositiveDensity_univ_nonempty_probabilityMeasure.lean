-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.univ_nonempty_probabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:41.136508+00:00
-- url     : https://prove2.me/submissions/034575c4-5e0c-4921-abe9-c9200592b80d

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
omit [TopologicalSpace α] [CompactSpace α] [PolishSpace α] [BorelSpace α]
  [OpensMeasurableSpace α]
namespace ChannelCapacity.Kernel.ContinuousPositiveDensity
theorem _root_.solution :
    (Set.univ : Set (ProbabilityMeasure α)).Nonempty := by
  exact ⟨MeasureTheory.diracProba (Classical.choice ‹Nonempty α›), Set.mem_univ _⟩
end ChannelCapacity.Kernel.ContinuousPositiveDensity
