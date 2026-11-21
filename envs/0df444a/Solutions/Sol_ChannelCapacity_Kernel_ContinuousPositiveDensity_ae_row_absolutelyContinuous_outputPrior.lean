-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.ae_row_absolutelyContinuous_outputPrior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:49.509358+00:00
-- url     : https://prove2.me/submissions/8798a37e-d2f0-4785-aa53-a61791724bde

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_row_absolutelyContinuous_ref
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_aemeasurable_outputDensity
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_outputPrior_eq_withDensity_outputDensity
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_outputDensity_pos
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
omit [CompactSpace β] [BorelSpace α] [BorelSpace β]
namespace ChannelCapacity.Kernel.ContinuousPositiveDensity
theorem _root_.solution
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    ∀ᵐ a ∂p.toMeasure, k a ≪ (outputPrior k p).toMeasure := by
  have hν_ac_out :
      ν ≪ (outputPrior k p).toMeasure := by
    have hν_ac_withDensity :
        ν ≪ ν.withDensity (h.outputDensity p) :=
      MeasureTheory.withDensity_absolutelyContinuous'
        (h.aemeasurable_outputDensity p)
        (Filter.Eventually.of_forall fun b => (h.outputDensity_pos p b).ne')
    simpa [h.outputPrior_eq_withDensity_outputDensity p] using hν_ac_withDensity
  exact Filter.Eventually.of_forall fun a =>
    (h.row_absolutelyContinuous_ref a).trans hν_ac_out
end ChannelCapacity.Kernel.ContinuousPositiveDensity
