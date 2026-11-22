-- Prove2me | solution 1 for ConfFamily.enables_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:23.182391+00:00
-- url     : https://prove2.me/submissions/213ea18f-d4f9-4aba-bf9e-5aad0797eca9

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
variable {F}
namespace ConfFamily
theorem _root_.solution {c : Set F.Event} {e : F.Event} (hc : F.Config c)
    (hx : F.Config (c ∪ {e})) : F.enables c e := ⟨hc, hx⟩
end ConfFamily
