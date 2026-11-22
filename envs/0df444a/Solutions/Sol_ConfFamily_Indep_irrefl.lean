-- Prove2me | solution 1 for ConfFamily.Indep.irrefl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:29.618675+00:00
-- url     : https://prove2.me/submissions/745f4f00-95f4-4818-9f11-374abd2dce1d

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
variable (F)
variable {F}
namespace ConfFamily
namespace Indep
theorem _root_.solution {c : Set F.Event} {e : F.Event} : ¬ F.Indep c e e :=
  fun h => h.1 rfl
end Indep
end ConfFamily
