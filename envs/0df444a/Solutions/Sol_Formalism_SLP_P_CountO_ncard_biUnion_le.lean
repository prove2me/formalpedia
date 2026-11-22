-- Prove2me | solution 1 for Formalism.SLP.P.CountO.ncard_biUnion_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:46:31.540669+00:00
-- url     : https://prove2.me/submissions/6d03a102-54dd-4086-a0cb-0e0ed3db9d64

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
open NumberField
variable (E : Type) [Field E] [NumberField E]
variable {E}
namespace Formalism.SLP.P.CountO
theorem _root_.solution {α β : Type} (s : Finset β) (t : β → Set α)
    (ht : ∀ b ∈ s, (t b).Finite) :
    (⋃ b ∈ s, t b).Finite ∧ (⋃ b ∈ s, t b).ncard ≤ ∑ b ∈ s, (t b).ncard := by
  classical
  refine ⟨s.finite_toSet.biUnion (fun b hb => ht b hb), ?_⟩
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    have ih' := ih (fun b hb => ht b (Finset.mem_insert_of_mem hb))
    calc (t a ∪ ⋃ b ∈ s, t b).ncard ≤ (t a).ncard + (⋃ b ∈ s, t b).ncard := Set.ncard_union_le _ _
      _ ≤ _ := Nat.add_le_add_left ih' _
end Formalism.SLP.P.CountO
