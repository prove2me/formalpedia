-- Prove2me | solution 1 for ChannelCapacity.conditionalEntropy_convexCombination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:36.148176+00:00
-- url     : https://prove2.me/submissions/93d9147a-31bd-45bf-a35e-07a731521179

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_convexCombination_toReal_apply

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
omit [MeasurableSingletonClass β]
namespace ChannelCapacity
theorem _root_.solution (p q : ProbabilityMeasure α) (k : Kernel α β)
    [IsMarkovKernel k] (t : NNReal) (ht : t ≤ (1 : NNReal)) :
    conditionalEntropy (ProbabilityMeasure.convexCombination p q t ht) k =
      (t : ℝ) * conditionalEntropy p k + (1 - (t : ℝ)) * conditionalEntropy q k := by
  unfold conditionalEntropy
  simp_rw [convexCombination_toReal_apply, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
end ChannelCapacity
