-- Prove2me | solution 1 for FamousTheorems.morita_equivalent_matrix_ring_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:24:23.264046+00:00
-- url     : https://prove2.me/submissions/8fe3d7a7-47cf-480c-a216-150e4e5f0216

import Mathlib

theorem solution (R : Type*) {ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι] (R₀ : Type*) [CommRing R₀] [Algebra R₀ R]
    [Nonempty ι] : IsMoritaEquivalent R₀ R (Matrix ι ι R) :=
  IsMoritaEquivalent.matrix R R₀
