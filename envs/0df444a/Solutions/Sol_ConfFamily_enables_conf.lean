-- Prove2me | solution 1 for ConfFamily.enables_conf
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T21:08:26.666719+00:00
-- url     : https://prove2.me/submissions/9d9573ed-09cf-498d-b7ec-304f477b301f

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

theorem ConfFamily.enables_conf {c : Set F.Event} {e : F.Event} (h : F.enables c e) : F.Config c := by
  exact h.1

theorem solution {c : Set F.Event} {e : F.Event} (h : F.enables c e) : F.Config c :=
  ConfFamily.enables_conf h
