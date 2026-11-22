-- Prove2me | solution 1 for ConfFamily.union_diff_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:02:55.548575+00:00
-- url     : https://prove2.me/submissions/71c79b82-9c5a-4938-94d7-d7793a100e60

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Stable_LTSI

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
variable {F}
namespace ConfFamily
theorem _root_.solution {c : Set F.Event} {e : F.Event} (he : e ∈ c) :
    (c \ {e}) ∪ {e} = c := by
  ext x
  constructor
  · rintro (⟨hx, -⟩ | hx)
    · exact hx
    · exact (Set.mem_singleton_iff.mp hx) ▸ he
  · intro hx
    by_cases hxe : x = e
    · exact Or.inr (Set.mem_singleton_iff.mpr hxe)
    · exact Or.inl ⟨hx, fun h => hxe (Set.mem_singleton_iff.mp h)⟩
end ConfFamily
