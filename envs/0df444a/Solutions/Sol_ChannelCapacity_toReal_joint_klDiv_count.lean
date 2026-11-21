-- Prove2me | solution 1 for ChannelCapacity.toReal_joint_klDiv_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:40.95162+00:00
-- url     : https://prove2.me/submissions/0597c898-53ef-4733-8643-869198d8b693

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_toReal_klDiv_count
public import Theorems.Thm_ChannelCapacity_absolutelyContinuous_count
public import Theorems.Thm_ChannelCapacity_klDiv_count_ne_top
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
public import Theorems.Thm_ProbabilityTheory_klDiv_compProd_right
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
theorem _root_.solution (k : Kernel α β) [IsMarkovKernel k] [Finite β]
    (p : ProbabilityMeasure α) :
    (InformationTheory.klDiv
        (jointLaw k p).toMeasure
        (p.toMeasure ⊗ₘ Kernel.const α Measure.count)).toReal =
      ∑ a, (p.toMeasure {a}).toReal *
        (InformationTheory.klDiv (k a) Measure.count).toReal := by
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  let _instCountableα : Countable α := by infer_instance
  let _instCountableβ : Countable β := by infer_instance
  have h_rows : ∀ᵐ a ∂p.toMeasure, k a ≪ Measure.count := by
    exact ae_of_all _ fun a => absolutelyContinuous_count (Kernel.rowProbabilityMeasure k a)
  have h_kl :
      InformationTheory.klDiv
          (jointLaw k p).toMeasure
          (p.toMeasure ⊗ₘ Kernel.const α Measure.count) =
        ∫⁻ a, InformationTheory.klDiv (k a) Measure.count ∂p.toMeasure := by
    apply ProbabilityTheory.klDiv_compProd_right
    exact Measure.AbsolutelyContinuous.compProd_right h_rows
  rw [h_kl]
  have hsum :
      ∫⁻ a, InformationTheory.klDiv (k a) Measure.count ∂p.toMeasure =
        ∑ a, InformationTheory.klDiv (k a) Measure.count * p.toMeasure {a} := by
    simpa [mul_comm] using
      (MeasureTheory.lintegral_fintype
        (μ := p.toMeasure)
        (f := fun a : α => InformationTheory.klDiv (k a) Measure.count))
  have hsum_toReal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum] at hsum_toReal
  · simpa [ENNReal.toReal_mul, Kernel.rowProbabilityMeasure, toReal_klDiv_count, mul_comm] using
      hsum_toReal
  · intro a _ha
    exact ENNReal.mul_ne_top
      (klDiv_count_ne_top (Kernel.rowProbabilityMeasure k a))
      (measure_ne_top _ _)
end ChannelCapacity
