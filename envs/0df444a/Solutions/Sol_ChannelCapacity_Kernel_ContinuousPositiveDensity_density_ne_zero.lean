-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.density_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:23.39548+00:00
-- url     : https://prove2.me/submissions/5b8b7080-c579-4b6f-ba92-f2df4fb68d11

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
theorem _root_.solution (h : ContinuousPositiveDensity k ν) (a : α) (b : β) :
    h.density a b ≠ 0 :=
  ne_of_gt (h.density_pos a b)
end ChannelCapacity.Kernel.ContinuousPositiveDensity
