-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.exists_uniform_density_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:17.366851+00:00
-- url     : https://prove2.me/submissions/de1d862c-50b9-471c-9ebd-129dfda2fc20

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
variable [CompactSpace α] [CompactSpace β] [Nonempty α] [Nonempty β]
namespace ChannelCapacity.Kernel.ContinuousPositiveDensity
theorem _root_.solution
    (h : ContinuousPositiveDensity k ν) :
    ∃ c C : NNReal,
      0 < c ∧ ∀ a b, c ≤ h.density a b ∧ h.density a b ≤ C := by
  let f : α × β → NNReal := Function.uncurry h.density
  obtain ⟨xMin, -, hxMin⟩ := IsCompact.exists_isMinOn (α := NNReal)
    (β := α × β) isCompact_univ Set.univ_nonempty h.continuous_density.continuousOn
  obtain ⟨xMax, -, hxMax⟩ := IsCompact.exists_isMaxOn (α := NNReal)
    (β := α × β) isCompact_univ Set.univ_nonempty h.continuous_density.continuousOn
  refine ⟨f xMin, f xMax, ?_, ?_⟩
  · simpa [f, Function.uncurry] using h.density_pos xMin.1 xMin.2
  · intro a b
    constructor
    · exact (isMinOn_univ_iff.mp hxMin) (a, b)
    · exact (isMaxOn_univ_iff.mp hxMax) (a, b)
end ChannelCapacity.Kernel.ContinuousPositiveDensity
