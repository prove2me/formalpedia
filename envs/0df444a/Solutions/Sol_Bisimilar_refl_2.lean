-- Prove2me | solution 2 for Bisimilar.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:57.431698+00:00
-- url     : https://prove2.me/submissions/3b978bbd-54fa-4bd1-8af2-ef870cecc6e7

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_LTS_Basic

set_option autoImplicit true
variable {L : Type*}
namespace Bisimilar
theorem _root_.solution (S : LTSI L) : Bisimilar S S := by
  refine ⟨Eq, rfl, ?_, ?_⟩
  · rintro s t a s' rfl hs; exact ⟨s', hs, rfl⟩
  · rintro s t a t' rfl ht; exact ⟨t', ht, rfl⟩
end Bisimilar
