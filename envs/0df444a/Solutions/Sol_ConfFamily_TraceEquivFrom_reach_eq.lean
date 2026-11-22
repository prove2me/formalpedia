-- Prove2me | solution 1 for ConfFamily.TraceEquivFrom.reach_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:06.206595+00:00
-- url     : https://prove2.me/submissions/5d56b50c-9016-4413-b46c-7a1fb3fe2d0f

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
import Theorems.Thm_ConfFamily_TraceEquivFrom_trans

set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
local infixr:60 " ≈ₜ " => TraceEquiv R
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open ConfFamily.TraceEquivFrom
namespace ConfFamily.TraceEquivFrom
theorem _root_.solution {c : Set F.Event} {t₁ t₂ : List F.Event} (h : TraceEquivFrom F c t₁ t₂) :
    reach F c t₁ = reach F c t₂ := by
  induction h with
  | refl => rfl
  | swap _ _ ih =>
    refine Eq.trans ?_ ih
    ext x; simp [reach]; tauto
end ConfFamily.TraceEquivFrom
