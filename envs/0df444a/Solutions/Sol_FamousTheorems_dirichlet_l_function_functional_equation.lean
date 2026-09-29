-- Prove2me | solution 1 for FamousTheorems.dirichlet_l_function_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:55:39.003202+00:00
-- url     : https://prove2.me/submissions/a173ced7-53d6-4c7c-b026-4bddd734b5f2

import Mathlib

theorem solution {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (s : ℂ) :
    DirichletCharacter.completedLFunction χ (1 - s) =
      (N : ℂ) ^ (s - 1 / 2) * χ.rootNumber * DirichletCharacter.completedLFunction χ⁻¹ s :=
  hχ.completedLFunction_one_sub s
