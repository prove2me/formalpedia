-- Prove2me | solution 1 for ChannelCapacity.Counterexample.priorCode_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:55.189945+00:00
-- url     : https://prove2.me/submissions/975c181b-fab8-4d1c-941c-086f7504f3f3

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
theorem _root_.solution :
    prior₁Code ≠ prior₂Code ∧ outputCode prior₁Code = outputCode prior₂Code := by
  refine ⟨?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    revert h0
    simp only [prior₁Code, prior₂Code]
    norm_num
  · funext y
    fin_cases y
    all_goals simp [outputCode, Fin.sum_univ_six, prior₁Code, prior₂Code, rowCode]
    all_goals norm_num
end ChannelCapacity.Counterexample
