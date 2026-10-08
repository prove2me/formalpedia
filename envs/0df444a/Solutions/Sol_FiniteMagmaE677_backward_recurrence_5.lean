-- Prove2me | solution 5 for FiniteMagmaE677.backward_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T05:47:38.74166+00:00
-- url     : https://prove2.me/submissions/4e54ece7-b1c3-4271-9f30-85031ec9601f

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
