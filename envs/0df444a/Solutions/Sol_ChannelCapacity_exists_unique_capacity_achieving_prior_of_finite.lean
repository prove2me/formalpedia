-- Prove2me | solution 1 for ChannelCapacity.exists_unique_capacity_achieving_prior_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:48:52.440648+00:00
-- url     : https://prove2.me/submissions/431be1ae-02bf-48cf-8cd8-7ce4a57058e3

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_Kernel_mutualInformation_strictlyConcave_of_rowMatrixFullRank
public import Theorems.Thm_ChannelCapacity_continuous_mutualInformation_of_finite
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_channelCapacity_eq_of_isMaxOn_univ
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
public import Theorems.Thm_ProbabilityMeasure_eq_of_isMaxOn_univ_of_strictConcave
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_dirac
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_id
attribute [local simp] ChannelCapacity.independentJointLaw_toMeasure
attribute [local simp] ChannelCapacity.jointLaw_toMeasure
attribute [local simp] ChannelCapacity.outputPrior_toMeasure
attribute [local simp] ProbabilityMeasure.convexCombination_toMeasure


section
@[expose] public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
namespace ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
namespace ProbabilityMeasure
end ProbabilityMeasure
namespace Kernel
end Kernel
section DiscreteKL
end DiscreteKL
section EntropyFormula
section FiniteWeakTopology
variable [TopologicalSpace α] [TopologicalSpace β]
  [DiscreteTopology α] [DiscreteTopology β]
  [BorelSpace α] [BorelSpace β]
  [CompactSpace α] [CompactSpace β]
end FiniteWeakTopology
section
omit [Fintype β] in
private lemma exists_unique_capacity_achieving_prior_of_finite_aux [Finite β]
    [Nonempty α] [TopologicalSpace α]
    [DiscreteTopology α] [T2Space α]
    [BorelSpace α] [CompactSpace α]
    (k : Kernel α β) [IsMarkovKernel k] (hRank : ChannelCapacity.Kernel.RowMatrixFullRank k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k := by
  have hcont : Continuous fun p : ProbabilityMeasure α => mutualInformation p k :=
    continuous_mutualInformation_of_finite k
  have hNonempty : (Set.univ : Set (ProbabilityMeasure α)).Nonempty := by
    refine ⟨MeasureTheory.diracProba (Classical.choice ‹Nonempty α›), by simp⟩
  obtain ⟨pMax, -, hpMax⟩ := IsCompact.exists_isMaxOn (α := ℝ)
    (β := ProbabilityMeasure α) isCompact_univ hNonempty hcont.continuousOn
  refine ⟨pMax, (channelCapacity_eq_of_isMaxOn_univ k hpMax).symm, ?_⟩
  intro q hq
  have hpMax' : ∀ p : ProbabilityMeasure α, mutualInformation p k ≤ mutualInformation pMax k :=
    isMaxOn_univ_iff.mp hpMax
  have hqMax : IsMaxOn (fun p : ProbabilityMeasure α => mutualInformation p k) Set.univ q := by
    apply isMaxOn_univ_iff.mpr
    intro p
    calc
      mutualInformation p k ≤ mutualInformation pMax k := hpMax' p
      _ = channelCapacity k := (channelCapacity_eq_of_isMaxOn_univ k hpMax).symm
      _ = mutualInformation q k := hq.symm
  exact ProbabilityMeasure.eq_of_isMaxOn_univ_of_strictConcave
    (p := pMax) (q := q)
    (Kernel.mutualInformation_strictlyConcave_of_rowMatrixFullRank k hRank) hpMax hqMax |>.symm
end
end EntropyFormula
end ChannelCapacity
end
end

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
theorem _root_.solution [Finite β]
    [Nonempty α] (k : Kernel α β) [IsMarkovKernel k]
    (hRank : ChannelCapacity.Kernel.RowMatrixFullRank k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k := by
  let : Fintype β := Fintype.ofFinite β
  let : TopologicalSpace α := ⊥
  let : TopologicalSpace β := ⊥
  let : DiscreteTopology α := ⟨rfl⟩
  let : DiscreteTopology β := ⟨rfl⟩
  let : T2Space α := by infer_instance
  let : T2Space β := by infer_instance
  let : BorelSpace α := by infer_instance
  let : BorelSpace β := by infer_instance
  let : CompactSpace α := Finite.compactSpace
  let : CompactSpace β := Finite.compactSpace
  exact exists_unique_capacity_achieving_prior_of_finite_aux k hRank
end ChannelCapacity
