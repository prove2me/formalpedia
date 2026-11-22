-- Prove2me | solution 1 for Bisimilar.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:36:41.609968+00:00
-- url     : https://prove2.me/submissions/014a780b-205b-4915-8900-4e8cd9bfe961

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_LTS_Basic

set_option autoImplicit true
variable {L : Type*}
namespace Bisimilar
theorem _root_.solution {S T : LTSI L} : Bisimilar S T → Bisimilar T S := by
  rintro ⟨R, hinit, hfwd, hbwd⟩
  exact ⟨fun t s => R s t, hinit, fun h hs => hbwd h hs, fun h ht => hfwd h ht⟩
end Bisimilar
