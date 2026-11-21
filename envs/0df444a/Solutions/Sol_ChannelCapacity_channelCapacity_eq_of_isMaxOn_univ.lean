-- Prove2me | solution 1 for ChannelCapacity.channelCapacity_eq_of_isMaxOn_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:09.589019+00:00
-- url     : https://prove2.me/submissions/b48ef7dc-c401-4cb1-a5cd-0758e4627da2

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
    {p : ProbabilityMeasure α}
    (hp : IsMaxOn (fun q => mutualInformation q k) Set.univ p) :
    channelCapacity k = mutualInformation p k := by
  let s : Set ℝ := Set.range fun q : ProbabilityMeasure α => mutualInformation q k
  have hp' : ∀ q : ProbabilityMeasure α, mutualInformation q k ≤ mutualInformation p k :=
    isMaxOn_univ_iff.mp hp
  have hsNonempty : s.Nonempty := ⟨mutualInformation p k, ⟨p, rfl⟩⟩
  have hsBdd : BddAbove s := by
    refine ⟨mutualInformation p k, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact hp' q
  apply le_antisymm
  · refine csSup_le hsNonempty ?_
    rintro _ ⟨q, rfl⟩
    exact hp' q
  · refine le_csSup hsBdd ?_
    exact ⟨p, rfl⟩
end ChannelCapacity
