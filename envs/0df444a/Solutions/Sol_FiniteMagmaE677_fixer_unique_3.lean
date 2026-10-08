-- Prove2me | solution 3 for FiniteMagmaE677.fixer_unique
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T02:06:24.236138+00:00
-- url     : https://prove2.me/submissions/aade3de2-b82c-4f31-ba3b-938ea4f49eb9

import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

universe u

theorem solution {α : Type u} [Fintype α] (op : α → α → α)
    (h : FiniteMagmaE677.E677 op) (x y : α) (hfix : op y x = x) :
    y = op (op x x) x := by
  have hinj (z : α) : Function.Injective (op z) := by
    apply Finite.injective_iff_surjective.mpr
    intro a
    exact ⟨op a (op (op z a) z), (h a z).symm⟩
  have inv_at_x : op y (op x (op x y)) = x := by
    have hi := (h x y).symm
    rwa [hfix] at hi
  have hx_xy := hinj y (hfix.trans inv_at_x.symm)
  exact hinj x (hinj x (hx_xy.symm.trans (h x x)))
