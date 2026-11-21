-- Prove2me | solution 1 for ChannelCapacity.toReal_outputPrior_apply_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:52.909979+00:00
-- url     : https://prove2.me/submissions/94c8528f-16e6-41db-9925-dbdc184da060

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_outputPrior_apply_singleton

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
omit [Fintype β]
namespace ChannelCapacity
theorem _root_.solution (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) (b : β) :
    ((outputPrior k p).toMeasure {b}).toReal =
      ∑ a, (p.toMeasure {a}).toReal * (k a {b}).toReal := by
  rw [outputPrior_apply_singleton]
  rw [ENNReal.toReal_sum]
  · simp_rw [ENNReal.toReal_mul]
  · intro a _ha
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
end ChannelCapacity
