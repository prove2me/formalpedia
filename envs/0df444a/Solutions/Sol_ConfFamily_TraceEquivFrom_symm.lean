-- Prove2me | solution 1 for ConfFamily.TraceEquivFrom.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:44:22.49413+00:00
-- url     : https://prove2.me/submissions/acbbc821-56c8-47b7-b80d-8d4279304844

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
import Theorems.Thm_ConfFamily_TraceEquivFrom_trans
import Theorems.Thm_ConfFamily_Indep_symm


set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
local infixr:60 " ≈ₜ " => TraceEquiv R
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open ConfFamily.TraceEquivFrom
namespace ConfFamily.TraceEquivFrom
theorem _root_.solution {c : Set F.Event} {t₁ t₂ : List F.Event} :
    TraceEquivFrom F c t₁ t₂ → TraceEquivFrom F c t₂ t₁ := by
  intro h
  induction h with
  | refl t => exact .refl t
  | swap ind _ ih => exact ih.trans (.swap ind.symm (.refl _))
end ConfFamily.TraceEquivFrom
