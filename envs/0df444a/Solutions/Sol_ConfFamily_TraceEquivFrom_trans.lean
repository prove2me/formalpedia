-- Prove2me | solution 1 for ConfFamily.TraceEquivFrom.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:42:53.005883+00:00
-- url     : https://prove2.me/submissions/a284f28c-fefc-4da9-aed3-f3532a5ec266

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
theorem _root_.solution {c : Set F.Event} {t₁ t₂ t₃ : List F.Event}
    (h₁₂ : TraceEquivFrom F c t₁ t₂) (h₂₃ : TraceEquivFrom F c t₂ t₃) :
    TraceEquivFrom F c t₁ t₃ := by
  induction h₁₂ with
  | refl _ => exact h₂₃
  | swap ind _ ih => exact .swap ind (ih h₂₃)
end ConfFamily.TraceEquivFrom
