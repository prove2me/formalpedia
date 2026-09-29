-- Prove2me | solution 1 for FiniteMagmaE677.exact_base_rows_give_fixer
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-15T04:35:20.03095+00:00
-- url     : https://prove2.me/submissions/5ad24c23-8415-4a95-8f9d-ea590f849151

import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

universe u

theorem solution
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x A c1 c3 c4 : α)
    (hxx : op x x = c1)
    (hxc3 : op x c3 = c4)
    (hc1x : op c1 x = c4)
    (hA_Ax : op A (op A x) = A)
    (hAA : op A A = c1)
    (hAx : op A x = c3)
    (hc3c3 : op c3 c3 = c1) :
    op (op (op x x) x) x = x := by
  have hinj : ∀ z : α, Function.Injective (op z) := by
    intro z
    have hs : Function.Surjective (op z) :=
      fun p => ⟨op p (op (op z p) z), (h p z).symm⟩
    exact (Finite.surjective_iff_bijective.mp hs).1
  have hAc3 : op A c3 = A := by
    rw [← hAx]
    exact hA_Ax
  have hc3c1 : op c3 c1 = x := by
    have hE := (h c3 A).symm
    rw [hAc3, hAA] at hE
    apply hinj A
    rw [hE, hAx]
  have hc1c4 : op c1 c4 = c3 := by
    have hE := h c1 c3
    rw [hc3c1, hxc3] at hE
    exact hinj c3 (hE.symm.trans hc3c3.symm)
  have hc4x : op c4 x = x := by
    have hE := h c4 c1
    rw [hc1c4, hc3c1] at hE
    exact hinj c1 (hE.symm.trans hc1x.symm)
  rw [hxx, hc1x, hc4x]
