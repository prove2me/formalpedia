-- Prove2me | solution 1 for ConsHalving.Additive.affine_comb_solves
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:59:20.946987+00:00
-- url     : https://prove2.me/submissions/72568dd2-9488-4758-98ac-b6a868345fff

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

open ConsHalving.Additive

theorem solution {n m : ℕ} (u : Fin n → Fin m → ℝ) (x y : Fin m → ℝ) (γ : ℝ)
    (hx : SolvesS u x) (hy : SolvesS u y) : SolvesS u (stepPoint x y γ) := by
  intro i
  have h1 := hx i
  have h2 := hy i
  have key : ∑ j, (stepPoint x y γ j - 1 / 2) * u i j =
      (1 - γ) * ∑ j, (x j - 1 / 2) * u i j + γ * ∑ j, (y j - 1 / 2) * u i j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold stepPoint
    ring
  rw [key, h1, h2]
  ring
