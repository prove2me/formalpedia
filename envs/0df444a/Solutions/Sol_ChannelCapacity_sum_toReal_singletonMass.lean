-- Prove2me | solution 1 for ChannelCapacity.sum_toReal_singletonMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:51.821208+00:00
-- url     : https://prove2.me/submissions/6b07951e-9790-45f0-b4e0-ff021c0c771e

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
namespace ChannelCapacity
theorem _root_.solution (μ : ProbabilityMeasure α) :
    ∑ a, (μ.toMeasure {a}).toReal = 1 := by
  have hprob_enn : ∑ a, μ.toMeasure {a} = (1 : ℝ≥0∞) := by
    calc
      ∑ a, μ.toMeasure {a} = ∑' a : α, μ.toMeasure {a} := by
        rw [← tsum_fintype
          (L := SummationFilter.unconditional _)
          (f := fun a : α => μ.toMeasure {a})]
      _ = μ.toMeasure Set.univ := by
        simpa only [Set.indicator_univ] using
          μ.toMeasure.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
      _ = 1 := by exact μ.prop.measure_univ
  rw [← ENNReal.toReal_sum (fun a _ha => measure_ne_top _ _), hprob_enn, ENNReal.toReal_one]
end ChannelCapacity
