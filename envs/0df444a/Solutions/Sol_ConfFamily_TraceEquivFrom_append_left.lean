-- Prove2me | solution 1 for ConfFamily.TraceEquivFrom.append_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:47:50.909788+00:00
-- url     : https://prove2.me/submissions/61408394-6b72-40c8-9fbb-5f649c762b75

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace

set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
local infixr:60 " ≈ₜ " => TraceEquiv R
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open ConfFamily.TraceEquivFrom
namespace ConfFamily.TraceEquivFrom
theorem _root_.solution {c : Set F.Event} {t₁ t₂ : List F.Event}
    (h : TraceEquivFrom F c t₁ t₂) (t : List F.Event) :
    TraceEquivFrom F c (t₁ ++ t) (t₂ ++ t) := by
  induction h with
  | refl _ => exact .refl _
  | @swap e₁ e₂ p s t' ind _ ih =>
    have h₁ : (p ++ e₂ :: e₁ :: s) ++ t = p ++ e₂ :: e₁ :: (s ++ t) := by simp
    have h₂ : (p ++ e₁ :: e₂ :: s) ++ t = p ++ e₁ :: e₂ :: (s ++ t) := by simp
    rw [h₁]
    exact .swap ind (h₂ ▸ ih)
end ConfFamily.TraceEquivFrom
