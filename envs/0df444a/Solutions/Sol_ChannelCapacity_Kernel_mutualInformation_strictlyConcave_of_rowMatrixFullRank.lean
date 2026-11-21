-- Prove2me | solution 1 for ChannelCapacity.Kernel.mutualInformation_strictlyConcave_of_rowMatrixFullRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:48:07.355932+00:00
-- url     : https://prove2.me/submissions/7d852a36-ea8e-4408-b2fe-e9bc93b4305e

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_conditionalEntropy_convexCombination
public import Theorems.Thm_ChannelCapacity_mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy
public import Theorems.Thm_ChannelCapacity_entropy_strictlyConcave
public import Theorems.Thm_ChannelCapacity_Kernel_injectivePriorPushforward_of_rowMatrixFullRank
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_convexCombination
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
theorem _root_.solution [Finite β]
    (k : Kernel α β) [IsMarkovKernel k] (hRank : ChannelCapacity.Kernel.RowMatrixFullRank k) :
    ∀ (p q : ProbabilityMeasure α) (_h_ne : p ≠ q) (t : NNReal)
      (_ht_pos : 0 < t) (ht_lt_one : t < 1),
      mutualInformation (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) k >
        (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k := by
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  intro p q h_ne t ht_pos ht_lt_one
  have hPush : Kernel.InjectivePriorPushforward k :=
    Kernel.injectivePriorPushforward_of_rowMatrixFullRank k hRank
  have hOut_ne : outputPrior k p ≠ outputPrior k q := by
    intro hEq
    exact h_ne (hPush hEq)
  have hEntropy :
      ProbabilityMeasure.entropy
          (ProbabilityMeasure.convexCombination (outputPrior k p) (outputPrior k q) t
            (le_of_lt ht_lt_one)) >
        (t : ℝ) * ProbabilityMeasure.entropy (outputPrior k p) +
          (1 - (t : ℝ)) * ProbabilityMeasure.entropy (outputPrior k q) :=
    entropy_strictlyConcave (outputPrior k p) (outputPrior k q) hOut_ne t ht_pos ht_lt_one
  calc
    mutualInformation (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) k =
        ProbabilityMeasure.entropy
            (ProbabilityMeasure.convexCombination (outputPrior k p) (outputPrior k q) t
              (le_of_lt ht_lt_one)) -
          ((t : ℝ) * conditionalEntropy p k + (1 - (t : ℝ)) * conditionalEntropy q k) := by
            rw [mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy]
            rw [conditionalEntropy_convexCombination]
            simpa [Kernel.priorPushforward] using
              congrArg ProbabilityMeasure.entropy
                (Kernel.priorPushforward_convexCombination k p q t (le_of_lt ht_lt_one))
    _ > ((t : ℝ) * ProbabilityMeasure.entropy (outputPrior k p) +
            (1 - (t : ℝ)) * ProbabilityMeasure.entropy (outputPrior k q)) -
          ((t : ℝ) * conditionalEntropy p k + (1 - (t : ℝ)) * conditionalEntropy q k) := by
            gcongr
    _ = (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k := by
          rw [mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy,
            mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy]
          ring
end Kernel
end ChannelCapacity
