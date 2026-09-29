-- Prove2me | solution 1 for FiniteMagmaE677.backward_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-11T01:04:28.948237+00:00
-- url     : https://prove2.me/submissions/4c25e992-978f-4b77-adc0-6d6e2c3808ca

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
