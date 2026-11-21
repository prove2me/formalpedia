-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.density_ennreal_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:29.486185+00:00
-- url     : https://prove2.me/submissions/e4dd72a1-a9bf-426a-8db1-cadf71e16a6b

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
    0 < (h.density a b : ENNReal) :=
  ENNReal.coe_pos.mpr (h.density_pos a b)
end ChannelCapacity.Kernel.ContinuousPositiveDensity
