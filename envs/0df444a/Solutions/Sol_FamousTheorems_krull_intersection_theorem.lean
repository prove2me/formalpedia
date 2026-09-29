-- Prove2me | solution 1 for FamousTheorems.krull_intersection_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:17:33.95891+00:00
-- url     : https://prove2.me/submissions/c040f690-dcd0-4fa4-97a1-99cb0d552ddc

import Mathlib

theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ⨅ i : ℕ, I ^ i = ⊥ :=
  Ideal.iInf_pow_eq_bot_of_isLocalRing I hI
