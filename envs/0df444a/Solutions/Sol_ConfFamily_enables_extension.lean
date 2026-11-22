-- Prove2me | solution 1 for ConfFamily.enables_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:38:34.299426+00:00
-- url     : https://prove2.me/submissions/26d84207-e5f7-4255-b14f-3f63fe15903c

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
theorem _root_.solution {c : Set F.Event} {e : F.Event} (h : F.enables c e) :
    F.Config (c ∪ {e}) := h.2
end ConfFamily
