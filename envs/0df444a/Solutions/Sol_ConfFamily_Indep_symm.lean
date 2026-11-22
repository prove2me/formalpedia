-- Prove2me | solution 1 for ConfFamily.Indep.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:39:24.964079+00:00
-- url     : https://prove2.me/submissions/176b588b-8e6a-44d3-aa4c-c4d5b4a1582b

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Theorems.Thm_ConfFamily_union_pair_comm

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
variable {F}
variable (F)
variable {F}
namespace ConfFamily
namespace Indep
theorem _root_.solution {c : Set F.Event} {e₁ e₂ : F.Event} (h : F.Indep c e₁ e₂) :
    F.Indep c e₂ e₁ :=
  ⟨h.1.symm, h.2.2.1, h.2.1, by rw [union_pair_comm]; exact h.2.2.2⟩
end Indep
end ConfFamily
