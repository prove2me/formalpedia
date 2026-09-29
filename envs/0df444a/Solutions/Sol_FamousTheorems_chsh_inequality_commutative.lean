-- Prove2me | solution 1 for FamousTheorems.chsh_inequality_commutative
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:14:46.186701+00:00
-- url     : https://prove2.me/submissions/0bc78dd4-3da0-4dbf-8297-fc1066b27825

import Mathlib

theorem solution {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R] [Algebra ℝ R]
    [IsOrderedModule ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 :=
  CHSH_inequality_of_comm A₀ A₁ B₀ B₁ T
