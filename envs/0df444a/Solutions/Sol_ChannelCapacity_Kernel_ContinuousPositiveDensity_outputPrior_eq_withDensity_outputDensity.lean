-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.outputPrior_eq_withDensity_outputDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:38.287193+00:00
-- url     : https://prove2.me/submissions/b730c735-41f9-4e97-9df5-157029a0299b

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_row_eq_withDensity
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
attribute [local simp] ChannelCapacity.outputPrior_toMeasure



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
theorem _root_.solution
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    (outputPrior k p).toMeasure = ν.withDensity (h.outputDensity p) := by
  ext s hs
  rw [outputPrior_toMeasure, Measure.bind_apply hs k.aemeasurable,
    MeasureTheory.withDensity_apply _ hs]
  simp_rw [h.row_eq_withDensity]
  simp_rw [MeasureTheory.withDensity_apply _ hs]
  have hbase :
      AEMeasurable
        (Function.uncurry fun a b => (h.density a b : ENNReal))
        (p.toMeasure.prod (ν.restrict s)) := by
    exact (ENNReal.continuous_coe.comp h.continuous_density).aemeasurable
  exact (lintegral_lintegral_swap (μ := p.toMeasure) (ν := ν.restrict s)
      (f := fun a b => (h.density a b : ENNReal)) hbase)
end ChannelCapacity.Kernel.ContinuousPositiveDensity
