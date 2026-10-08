-- Prove2me | solution 3 for FiniteMagmaE677.backward_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T02:01:41.088726+00:00
-- url     : https://prove2.me/submissions/ae5733de-8985-4f1c-9779-c472d523c3ea

import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

universe u

theorem solution {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x y : α) :
    x = op (op y x) (op (op y (op y x)) y) := by
  have hinj (z : α) : Function.Injective (op z) := by
    apply Finite.injective_iff_surjective.mpr
    intro a
    exact ⟨op a (op (op z a) z), (h a z).symm⟩
  exact hinj y (h (op y x) y)
