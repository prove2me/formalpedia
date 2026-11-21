-- Prove2me | solution 1 for ChannelCapacity.Kernel.injectivePriorPushforward_of_rowMatrixFullRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:37.434972+00:00
-- url     : https://prove2.me/submissions/54d682ce-c703-4fae-8c67-b3607bbc17eb

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_toReal_outputPrior_apply_singleton
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
namespace Kernel
theorem _root_.solution
    (k : Kernel α β) [IsMarkovKernel k] (hRank : ChannelCapacity.Kernel.RowMatrixFullRank k) :
    Kernel.InjectivePriorPushforward k := by
  intro p q hpq
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  have hrowEq :
      ∀ b : β,
        ∑ a, ((p.toMeasure {a}).toReal - (q.toMeasure {a}).toReal) * (k a {b}).toReal = 0 := by
    intro b
    have hb :
        ((outputPrior k p).toMeasure {b}).toReal = ((outputPrior k q).toMeasure {b}).toReal := by
      simpa [Kernel.priorPushforward] using
        congrArg (fun μ : ProbabilityMeasure β => ((μ.toMeasure {b}).toReal)) hpq
    rw [toReal_outputPrior_apply_singleton, toReal_outputPrior_apply_singleton] at hb
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hb
  have hweights :
      (fun a' : α => (p.toMeasure {a'}).toReal - (q.toMeasure {a'}).toReal) = 0 := by
    apply hRank
    funext b
    simpa using hrowEq b
  have ha_toReal : (p.toMeasure {a}).toReal = (q.toMeasure {a}).toReal := by
    have ha_sub : (p.toMeasure {a}).toReal - (q.toMeasure {a}).toReal = 0 := by
      simpa using congrArg (fun w : α → ℝ => w a) hweights
    exact sub_eq_zero.mp ha_sub
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp ha_toReal
end Kernel
end ChannelCapacity
