-- Prove2me | solution 2 for ConsHalving.Additive.affine_comb_solves
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:19:37.546298+00:00
-- url     : https://prove2.me/submissions/bdfe99a0-4b32-458e-ab88-83f181662055

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

set_option autoImplicit false
open ConsHalving.Additive

theorem solution {n m : ℕ} (u : Fin n → Fin m → ℝ) (x y : Fin m → ℝ) (γ : ℝ)
    (hx : SolvesS u x) (hy : SolvesS u y) : SolvesS u (stepPoint x y γ) := by
  intro i
  have h1 := hx i
  have h2 := hy i
  have : ∑ j, (stepPoint x y γ j - 1/2) * u i j
      = (1-γ) * ∑ j, (x j - 1/2) * u i j + γ * ∑ j, (y j - 1/2) * u i j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [stepPoint]; ring
  rw [this, h1, h2]; ring
