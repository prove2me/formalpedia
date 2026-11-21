-- Prove2me | solution 1 for ChannelCapacity.convexCombination_toReal_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:47.778183+00:00
-- url     : https://prove2.me/submissions/6ed0c604-2e65-4b30-a3ec-d11b316801ca

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
public import Theorems.Thm_ProbabilityMeasure_convexCombination_apply
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
theorem _root_.solution (p q : ProbabilityMeasure α) (t : NNReal)
    (ht : t ≤ (1 : NNReal)) (a : α) :
    ((ProbabilityMeasure.convexCombination p q t ht).toMeasure {a}).toReal =
      (t : ℝ) * (p.toMeasure {a}).toReal + (1 - (t : ℝ)) * (q.toMeasure {a}).toReal := by
  rw [ProbabilityMeasure.convexCombination_apply _ _ _ _ (measurableSet_singleton a)]
  have hp_fin : p.toMeasure {a} ≠ ∞ := measure_ne_top _ _
  have hq_fin : q.toMeasure {a} ≠ ∞ := measure_ne_top _ _
  have hleft_fin : ((t : ENNReal) * p.toMeasure {a}) ≠ ∞ := ENNReal.mul_ne_top (by simp) hp_fin
  have hright_fin :
      ((((1 : NNReal) - t : NNReal) : ENNReal) * q.toMeasure {a}) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hq_fin
  rw [ENNReal.toReal_add hleft_fin hright_fin, ENNReal.toReal_mul, ENNReal.toReal_mul]
  change (t : ℝ) * (p.toMeasure {a}).toReal + (((1 : NNReal) - t : NNReal) : ℝ) *
      (q.toMeasure {a}).toReal =
    (t : ℝ) * (p.toMeasure {a}).toReal + (1 - (t : ℝ)) * (q.toMeasure {a}).toReal
  rw [NNReal.coe_sub ht]
  simp
end ChannelCapacity
