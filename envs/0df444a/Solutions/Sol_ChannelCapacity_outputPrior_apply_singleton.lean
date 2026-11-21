-- Prove2me | solution 1 for ChannelCapacity.outputPrior_apply_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:55.960174+00:00
-- url     : https://prove2.me/submissions/31532e73-8e48-415d-8aea-46757837fb76

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_dirac
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_id
attribute [local simp] ChannelCapacity.independentJointLaw_toMeasure
attribute [local simp] ChannelCapacity.jointLaw_toMeasure
attribute [local simp] ChannelCapacity.outputPrior_toMeasure
attribute [local simp] ProbabilityMeasure.convexCombination_toMeasure



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
    (outputPrior k p).toMeasure {b} = ∑ a, p.toMeasure {a} * k a {b} := by
  calc
    (outputPrior k p).toMeasure {b}
      = (Measure.sum fun a : α => p.toMeasure {a} • k a) {b} := by
          rw [outputPrior_toMeasure, Measure.comp_eq_sum_of_countable]
    _ = ∑' a : α, (p.toMeasure {a} • k a) {b} := by
          rw [Measure.sum_apply _ (measurableSet_singleton b)]
    _ = ∑' a : α, p.toMeasure {a} * k a {b} := by
          simp [Measure.smul_apply]
    _ = ∑ a, p.toMeasure {a} * k a {b} := by
          rw [tsum_fintype]
end ChannelCapacity
