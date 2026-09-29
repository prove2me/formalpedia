-- Prove2me | solution 1 for FamousTheorems.tsirelson_inequality_chsh
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:14:28.415024+00:00
-- url     : https://prove2.me/submissions/d93c4e2f-b988-4194-a145-4c8f0968cd20

import Mathlib

theorem solution {R : Type*} [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] [Algebra ℝ R]
    [IsOrderedModule ℝ R] [StarModule ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ Real.sqrt 2 ^ 3 • (1 : R) :=
  tsirelson_inequality A₀ A₁ B₀ B₁ T
