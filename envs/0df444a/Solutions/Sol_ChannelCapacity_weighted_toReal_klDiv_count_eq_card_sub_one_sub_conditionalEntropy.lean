-- Prove2me | solution 1 for ChannelCapacity.weighted_toReal_klDiv_count_eq_card_sub_one_sub_conditionalEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:36.374484+00:00
-- url     : https://prove2.me/submissions/2ba4950f-6c38-4366-8788-03100cbaaa6e

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_sum_toReal_singletonMass
public import Theorems.Thm_ChannelCapacity_Kernel_toReal_klDiv_count_eq_card_sub_one_sub_rowEntropy

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
namespace ChannelCapacity
theorem _root_.solution
    (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    ∑ a, (p.toMeasure {a}).toReal * (InformationTheory.klDiv (k a) Measure.count).toReal =
      (Fintype.card β : ℝ) - 1 - conditionalEntropy p k := by
  have hprob := sum_toReal_singletonMass p
  calc
    ∑ a, (p.toMeasure {a}).toReal * (InformationTheory.klDiv (k a) Measure.count).toReal
      = ∑ a, (p.toMeasure {a}).toReal *
          ((Fintype.card β : ℝ) - 1 - Kernel.rowEntropy k a) := by
            simp_rw [Kernel.toReal_klDiv_count_eq_card_sub_one_sub_rowEntropy]
    _ = ∑ a,
          ((p.toMeasure {a}).toReal * ((Fintype.card β : ℝ) - 1) -
            (p.toMeasure {a}).toReal * Kernel.rowEntropy k a) := by
          simp_rw [mul_sub]
    _ = (∑ a, (p.toMeasure {a}).toReal * ((Fintype.card β : ℝ) - 1)) -
          ∑ a, (p.toMeasure {a}).toReal * Kernel.rowEntropy k a := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ a, (p.toMeasure {a}).toReal) * ((Fintype.card β : ℝ) - 1) -
          conditionalEntropy p k := by
          rw [Finset.sum_mul, conditionalEntropy]
    _ = (Fintype.card β : ℝ) - 1 - conditionalEntropy p k := by
          rw [hprob]
          ring
end ChannelCapacity
