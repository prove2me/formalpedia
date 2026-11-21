-- Prove2me | solution 1 for ChannelCapacity.ProbabilityMeasure.integral_eq_sum_singletonMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:14.529415+00:00
-- url     : https://prove2.me/submissions/f4f26c53-cd13-464e-929e-c8d158622f3e

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
variable [TopologicalSpace α] [TopologicalSpace β]
  [DiscreteTopology α] [DiscreteTopology β]
  [BorelSpace α] [BorelSpace β]
  [CompactSpace α] [CompactSpace β]
omit [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α] [CompactSpace α]
namespace ChannelCapacity
namespace ProbabilityMeasure
theorem _root_.solution (μ : ProbabilityMeasure α) (f : α → ℝ) :
    ∫ a, f a ∂μ.toMeasure = ∑ a, (μ.toMeasure {a}).toReal * f a := by
  have hf : Integrable f μ.toMeasure := by
    have hf_simple :
        Integrable (MeasureTheory.SimpleFunc.ofFinite f : α → ℝ) μ.toMeasure :=
      (MeasureTheory.SimpleFunc.integrable_of_isFiniteMeasure
        (μ := μ.toMeasure) (MeasureTheory.SimpleFunc.ofFinite f))
    exact hf_simple
  simpa [measureReal_def, smul_eq_mul] using
    (MeasureTheory.integral_fintype (μ := μ.toMeasure) (f := f) hf)
end ProbabilityMeasure
end ChannelCapacity
