-- Prove2me | solution 1 for ChannelCapacity.exists_unique_capacity_achieving_prior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:15.362656+00:00
-- url     : https://prove2.me/submissions/09677893-44b1-4f55-a890-5d4dab4f35fc

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Theorems.Thm_ChannelCapacity_channelCapacity_eq_of_isMaxOn_univ
public import Theorems.Thm_ChannelCapacity_exists_isMaxOn_mutualInformation
public import Theorems.Thm_ChannelCapacity_Kernel_mutualInformation_strictlyConcave_of_injectivePriorPushforward
public import Theorems.Thm_ProbabilityMeasure_eq_of_isMaxOn_univ_of_strictConcave


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open ChannelCapacity
open ProbabilityMeasure
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
namespace ChannelCapacity
theorem _root_.solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (k : Kernel α β) [IsMarkovKernel k]
    (h : Kernel.InjectivePriorPushforward k)
    (hWC : Kernel.WellConditionedForCapacity k)
    [TopologicalSpace (ProbabilityMeasure α)]
    (hNonempty : (Set.univ : Set (ProbabilityMeasure α)).Nonempty)
    (hCompact : IsCompact (Set.univ : Set (ProbabilityMeasure α)))
    (hUsc : UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k := by
  rcases exists_isMaxOn_mutualInformation k hNonempty hCompact hUsc with ⟨pMax, hpMax⟩
  refine ⟨pMax, (channelCapacity_eq_of_isMaxOn_univ k hpMax).symm, ?_⟩
  intro p hp
  have hpMax' : ∀ q : ProbabilityMeasure α, mutualInformation q k ≤ mutualInformation pMax k :=
    isMaxOn_univ_iff.mp hpMax
  have hp' : IsMaxOn (fun q => mutualInformation q k) Set.univ p := by
    intro q _hq
    calc
      mutualInformation q k ≤ mutualInformation pMax k := hpMax' q
      _ = channelCapacity k := (channelCapacity_eq_of_isMaxOn_univ k hpMax).symm
      _ = mutualInformation p k := hp.symm
  exact ProbabilityMeasure.eq_of_isMaxOn_univ_of_strictConcave
    (Kernel.mutualInformation_strictlyConcave_of_injectivePriorPushforward k h hWC) hp' hpMax
end ChannelCapacity
