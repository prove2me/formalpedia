-- Prove2me | solution 1 for FiniteMagmaE677.no_left_period_two
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:54:35.653121+00:00
-- url     : https://prove2.me/submissions/8ef3acad-511e-4e38-ac55-c38f77c4cfa3

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_fixer_unique

/-!
# No element of a finite E677 magma has left-orbit period exactly two

Write `L_x z = x ⋄ z` and suppose `x ⋄ (x ⋄ x) = x` with `z₁ := x ⋄ x`.
E677 instantiated at `(x, x)` reads `x = L_x (L_x c₁)` where
`c₁ = (x ⋄ x) ⋄ x = z₁ ⋄ x`, while the hypothesis reads `x = L_x (L_x x)`.
Left cancellation (two steps) gives `c₁ = x`, i.e. `z₁ ⋄ x = x`: the
successor `z₁` is a fixer of `x`. By fixer uniqueness the fixer must equal
`c₁` itself, so `z₁ = c₁ = x`, contradicting `z₁ ≠ x`. Hence the orbit of
`x` under `L_x` cannot have exact period two: `x ⋄ (x ⋄ x) = x` forces
`x ⋄ x = x`.
-/

universe u

theorem FiniteMagmaE677.no_left_period_two {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x : α)
    (hper : op x (op x x) = x) : op x x = x := by
  by_contra hni
  have hinj := (FiniteMagmaE677.left_bijective op h x).1
  -- E677 at (x, x): x = op x (op x ((x ⋄ x) ⋄ x))
  have hE := h x x
  -- hper and hE are two decompositions of x as L_x (L_x ·)
  have key : op x (op x (op (op x x) x)) = op x (op x x) := hE.symm.trans hper.symm
  have step1 := hinj key
  have hc1 : op (op x x) x = x := hinj step1
  -- the successor z₁ := x ⋄ x fixes x; but the only possible fixer is c₁ = x
  exact hni ((FiniteMagmaE677.fixer_unique op h x (op x x) hc1).trans hc1)

theorem solution {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x : α)
    (hper : op x (op x x) = x) : op x x = x :=
  FiniteMagmaE677.no_left_period_two op h x hper
