-- Prove2me | solution 2 for ConfFamily.enables_conf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:17.910362+00:00
-- url     : https://prove2.me/submissions/cee71acc-028b-4a93-8a8e-484a58d4c6bf

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
theorem _root_.solution {c : Set F.Event} {e : F.Event} (h : F.enables c e) : F.Config c := h.1
end ConfFamily
