-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.hFiniteRefKL_of_continuousPositiveDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:43.615091+00:00
-- url     : https://prove2.me/submissions/e3e6b9b2-7d16-470b-be11-c1fc0b25b0c2

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_ae_row_absolutelyContinuous_outputPrior
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_row_klDiv_le_outputPrior_bound
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
omit [BorelSpace α]
namespace ChannelCapacity.Kernel.ContinuousPositiveDensity
theorem _root_.solution
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) (ν' : Measure β)
    (hRef : Kernel.OutputMarginalReference k p ν') :
    InformationTheory.klDiv (p.toMeasure ⊗ₘ k) (p.toMeasure ⊗ₘ Kernel.const _ ν') ≠ ∞ := by
  rcases hRef with ⟨q, hpq, rfl⟩
  rcases h.row_klDiv_le_outputPrior_bound q with ⟨B, hB_fin, hB⟩
  have hp_rows : ∀ᵐ a ∂p.toMeasure, k a ≪ (outputPrior k q).toMeasure := by
    rw [ae_iff]
    exact hpq (by simpa [ae_iff] using h.ae_row_absolutelyContinuous_outputPrior q)
  have h_ac :
      p.toMeasure ⊗ₘ k ≪ p.toMeasure ⊗ₘ Kernel.const α (outputPrior k q).toMeasure :=
    Measure.AbsolutelyContinuous.compProd_right hp_rows
  have h_le :
      InformationTheory.klDiv (p.toMeasure ⊗ₘ k)
          (p.toMeasure ⊗ₘ Kernel.const α (outputPrior k q).toMeasure) ≤
        B := by
    rw [ProbabilityTheory.klDiv_compProd_right (μ := p.toMeasure)
      (κ := k) (η := Kernel.const α (outputPrior k q).toMeasure) h_ac]
    calc
      ∫⁻ a, InformationTheory.klDiv (k a) ((Kernel.const α (outputPrior k q).toMeasure) a)
          ∂p.toMeasure ≤
        ∫⁻ _, B ∂p.toMeasure := by
          refine lintegral_mono ?_
          intro a
          simpa using hB a
      _ = B := by simp
  exact ne_top_of_le_ne_top hB_fin h_le
end ChannelCapacity.Kernel.ContinuousPositiveDensity
