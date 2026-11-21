-- Prove2me | solution 1 for ChannelCapacity.mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:22.093985+00:00
-- url     : https://prove2.me/submissions/24598ce6-4556-403d-b751-ce7da26c7303

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_toReal_klDiv_count
public import Theorems.Thm_ChannelCapacity_weighted_toReal_klDiv_count_eq_card_sub_one_sub_conditionalEntropy
public import Theorems.Thm_ChannelCapacity_klDiv_count_ne_top
public import Theorems.Thm_ChannelCapacity_joint_klDiv_count_ne_top
public import Theorems.Thm_ChannelCapacity_toReal_joint_klDiv_count
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_klDiv_mutualInformation_chain
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
theorem _root_.solution
    (k : Kernel α β) [IsMarkovKernel k] [Finite β] (p : ProbabilityMeasure α) :
    mutualInformation p k =
      ProbabilityMeasure.entropy (outputPrior k p) - conditionalEntropy p k := by
  let _instCountableα : Countable α := by infer_instance
  let _instCountableβ : Countable β := by infer_instance
  let _instDiscreteMeasurableα : DiscreteMeasurableSpace α := by infer_instance
  let _instStandardBorelα : StandardBorelSpace α := by infer_instance
  let _instNonemptyα : Nonempty α := p.nonempty
  have h_chain :=
    klDiv_mutualInformation_chain (k := k) (p := p) (ν := Measure.count)
  have h_left_fin : InformationTheory.klDiv
      (jointLaw k p).toMeasure
      (p.toMeasure ⊗ₘ Kernel.const α Measure.count) ≠ ∞ :=
    joint_klDiv_count_ne_top k p
  have h_out_fin : InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count ≠ ∞ :=
    klDiv_count_ne_top (outputPrior k p)
  have h_mi_fin :
      InformationTheory.klDiv
          (jointLaw k p).toMeasure
          (independentJointLaw k p).toMeasure ≠ ∞ := by
    intro h_top
    have h_left_top :
        InformationTheory.klDiv
            (jointLaw k p).toMeasure
            (p.toMeasure ⊗ₘ Kernel.const α Measure.count) = ∞ := by
      calc
        InformationTheory.klDiv
            (jointLaw k p).toMeasure
            (p.toMeasure ⊗ₘ Kernel.const α Measure.count)
            =
              InformationTheory.klDiv
                (jointLaw k p).toMeasure
                (independentJointLaw k p).toMeasure +
                  InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count := h_chain
        _ = ∞ + InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count := by rw [h_top]
        _ = ∞ := by simp
    exact h_left_fin h_left_top
  have h_chain_real : (InformationTheory.klDiv
      (jointLaw k p).toMeasure
      (p.toMeasure ⊗ₘ Kernel.const α Measure.count)).toReal =
        mutualInformation p k +
          (InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count).toReal := by
    have h_chain_real' := congrArg ENNReal.toReal h_chain
    rw [ENNReal.toReal_add h_mi_fin h_out_fin] at h_chain_real'
    simpa [mutualInformation, jointLaw_toMeasure, independentJointLaw_toMeasure,
      outputPrior_toMeasure]
      using h_chain_real'
  have h_output :
      (InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count).toReal =
        (Fintype.card β : ℝ) - 1 - ProbabilityMeasure.entropy (outputPrior k p) := by
    simpa [ProbabilityMeasure.entropy] using toReal_klDiv_count (outputPrior k p)
  rw [toReal_joint_klDiv_count,
    weighted_toReal_klDiv_count_eq_card_sub_one_sub_conditionalEntropy, h_output] at h_chain_real
  have h_formula :
      mutualInformation p k =
        ProbabilityMeasure.entropy (outputPrior k p) - conditionalEntropy p k := by
    linarith
  linarith
end ChannelCapacity
