-- Prove2me | solution 1 for ChannelCapacity.exists_isMaxOn_mutualInformation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:38.526186+00:00
-- url     : https://prove2.me/submissions/34e21784-ee60-4dd3-9d50-37407a03d32c

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity

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
    ∃ p : ProbabilityMeasure α,
      IsMaxOn (fun q => mutualInformation q k) Set.univ p := by
  rcases UpperSemicontinuousOn.exists_isMaxOn
      (f := fun p : ProbabilityMeasure α => mutualInformation p k)
      (s := (Set.univ : Set (ProbabilityMeasure α)))
      hNonempty hCompact (hUsc.upperSemicontinuousOn _) with ⟨p, _hp, hp⟩
  exact ⟨p, hp⟩
end ChannelCapacity
