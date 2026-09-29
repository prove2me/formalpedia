-- Prove2me | solution 1 for FamousTheorems.krull_principal_ideal_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:20:58.548953+00:00
-- url     : https://prove2.me/submissions/5629a513-4762-496f-abb7-3ca2a158d990

import Mathlib

theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [Submodule.IsPrincipal I] :
    ∀ p ∈ I.minimalPrimes, p.height ≤ 1 :=
  Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I
