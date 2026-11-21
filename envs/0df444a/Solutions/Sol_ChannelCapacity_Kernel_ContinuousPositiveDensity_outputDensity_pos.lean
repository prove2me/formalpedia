-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.outputDensity_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:46.117821+00:00
-- url     : https://prove2.me/submissions/035197a2-4532-4f57-98c8-6648f857da61

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
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
omit [CompactSpace β] [PolishSpace α] [PolishSpace β] [BorelSpace α] [BorelSpace β]
  [OpensMeasurableSpace β] [IsFiniteMeasure ν]
namespace ChannelCapacity.Kernel.ContinuousPositiveDensity
theorem _root_.solution (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) (b : β) :
    0 < h.outputDensity p b := by
  let : Nonempty α := p.nonempty
  have hcont : Continuous fun a : α => h.density a b := by
    have hpair : Continuous fun a : α => (a, b) := by
      fun_prop
    exact h.continuous_density.comp hpair
  obtain ⟨a0, -, ha0⟩ := IsCompact.exists_isMinOn (α := NNReal)
    (β := α) isCompact_univ Set.univ_nonempty hcont.continuousOn
  have ha0' : ∀ a : α, h.density a0 b ≤ h.density a b :=
    isMinOn_univ_iff.mp ha0
  have hle : ∀ a : α, (h.density a0 b : ENNReal) ≤ (h.density a b : ENNReal) := by
    intro a
    exact_mod_cast ha0' a
  have hconst_le :
      (h.density a0 b : ENNReal) ≤ h.outputDensity p b := by
    calc
      (h.density a0 b : ENNReal) = ∫⁻ a, (h.density a0 b : ENNReal) ∂p.toMeasure := by simp
      _ ≤ ∫⁻ a, (h.density a b : ENNReal) ∂p.toMeasure := lintegral_mono hle
      _ = h.outputDensity p b := rfl
  exact lt_of_lt_of_le (ENNReal.coe_pos.mpr (h.density_pos a0 b)) hconst_le
end ChannelCapacity.Kernel.ContinuousPositiveDensity
