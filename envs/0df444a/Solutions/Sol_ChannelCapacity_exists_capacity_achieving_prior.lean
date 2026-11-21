-- Prove2me | solution 1 for ChannelCapacity.exists_capacity_achieving_prior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:34.082986+00:00
-- url     : https://prove2.me/submissions/7cb725e3-a500-4f1d-a93b-e9fb994e06df

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Theorems.Thm_ChannelCapacity_channelCapacity_eq_of_isMaxOn_univ
public import Theorems.Thm_ChannelCapacity_exists_isMaxOn_mutualInformation

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open ChannelCapacity
open ProbabilityMeasure
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
namespace ChannelCapacity
theorem _root_.solution (k : Kernel α β) [IsMarkovKernel k]
    [TopologicalSpace (ProbabilityMeasure α)]
    (hNonempty : (Set.univ : Set (ProbabilityMeasure α)).Nonempty)
    (hCompact : IsCompact (Set.univ : Set (ProbabilityMeasure α)))
    (hUsc : UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k) :
    ∃ p : ProbabilityMeasure α, IsCapacityAchievingPrior k p := by
  rcases exists_isMaxOn_mutualInformation k hNonempty hCompact hUsc with ⟨p, hp⟩
  exact ⟨p, (channelCapacity_eq_of_isMaxOn_univ k hp).symm⟩
end ChannelCapacity
