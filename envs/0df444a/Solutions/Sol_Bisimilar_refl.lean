-- Prove2me | solution 1 for Bisimilar.refl
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T21:05:48.422057+00:00
-- url     : https://prove2.me/submissions/431b6319-02f7-4702-bd2f-884c423c9758

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_LTS_Basic
set_option autoImplicit true
variable {L : Type*}
theorem Bisimilar.refl (S : LTSI L) : Bisimilar S S :=
  ⟨Eq, ⟨rfl, fun {s t a s'} h hs => ⟨s', h ▸ hs, rfl⟩,
    fun {s t a t'} h ht => ⟨t', h ▸ ht, rfl⟩⟩⟩
theorem solution (S : LTSI L) : Bisimilar S S := Bisimilar.refl S
