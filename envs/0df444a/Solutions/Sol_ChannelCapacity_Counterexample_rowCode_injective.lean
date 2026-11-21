-- Prove2me | solution 1 for ChannelCapacity.Counterexample.rowCode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:05.912675+00:00
-- url     : https://prove2.me/submissions/07714fbe-8835-4620-b4db-9237de6c918b

module
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_Counterexample
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
open scoped ENNReal NNReal
open ChannelCapacity ChannelCapacity.Counterexample
namespace ChannelCapacity.Counterexample
theorem _root_.solution : Function.Injective rowCode := by
  intro a b hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  fin_cases a <;> fin_cases b <;>
    first
      | rfl
      | (exfalso; simp [rowCode] at h0 h1)
end ChannelCapacity.Counterexample
