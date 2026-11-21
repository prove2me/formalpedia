-- Prove2me | solution 1 for ChannelCapacity.rnDeriv_count_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:34.269388+00:00
-- url     : https://prove2.me/submissions/0c548b49-ae4b-484d-ad33-27c02e2e6a8a

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_toMeasure_eq_count_withDensity
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
omit [Fintype α]
namespace ChannelCapacity
theorem _root_.solution (μ : ProbabilityMeasure α) :
    [Countable α] →
      μ.toMeasure.rnDeriv Measure.count =ᵐ[Measure.count] fun a => μ.toMeasure {a} := by
  intro _instCountable
  have hcount :
      Measure.count.withDensity (fun a : α => μ.toMeasure {a}) = μ.toMeasure :=
    (toMeasure_eq_count_withDensity (μ := μ)).symm
  simpa [hcount] using
    (Measure.rnDeriv_withDensity
      (ν := Measure.count)
      (f := fun a : α => μ.toMeasure {a})
      (measurable_of_countable (fun a : α => μ.toMeasure {a})))
end ChannelCapacity
