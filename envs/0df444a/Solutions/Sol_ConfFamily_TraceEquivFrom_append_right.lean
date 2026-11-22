-- Prove2me | solution 1 for ConfFamily.TraceEquivFrom.append_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:48:50.189569+00:00
-- url     : https://prove2.me/submissions/aa6deb2e-ad1e-4f02-8f9b-9718073c4adc

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
import Theorems.Thm_reach_append

set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
local infixr:60 " ≈ₜ " => TraceEquiv R
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open ConfFamily.TraceEquivFrom
namespace ConfFamily.TraceEquivFrom
theorem _root_.solution {c : Set F.Event} (t : List F.Event) {t₁ t₂ : List F.Event}
    (h : TraceEquivFrom F (reach F c t) t₁ t₂) :
    TraceEquivFrom F c (t ++ t₁) (t ++ t₂) := by
  induction h with
  | refl _ => exact .refl _
  | @swap e₁ e₂ p s t' ind _ ih =>
    have h₁ : t ++ (p ++ e₂ :: e₁ :: s) = (t ++ p) ++ e₂ :: e₁ :: s := by simp
    have h₂ : t ++ (p ++ e₁ :: e₂ :: s) = (t ++ p) ++ e₁ :: e₂ :: s := by simp
    rw [h₁]
    exact .swap ((reach_append F c t p) ▸ ind) (h₂ ▸ ih)
end ConfFamily.TraceEquivFrom
