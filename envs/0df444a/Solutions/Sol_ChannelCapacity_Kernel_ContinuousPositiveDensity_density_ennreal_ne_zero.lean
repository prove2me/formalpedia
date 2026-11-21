-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.density_ennreal_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:23.93476+00:00
-- url     : https://prove2.me/submissions/3b231f9d-f4ad-4c74-b601-d8dd86ce0e26

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_density_ennreal_pos

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
    (h.density a b : ENNReal) ≠ 0 :=
  ne_of_gt (h.density_ennreal_pos a b)
end ChannelCapacity.Kernel.ContinuousPositiveDensity
