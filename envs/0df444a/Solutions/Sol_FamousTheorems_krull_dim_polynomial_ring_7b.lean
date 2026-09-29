-- Prove2me | solution 1 for FamousTheorems.krull_dim_polynomial_ring_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:58:10.770224+00:00
-- url     : https://prove2.me/submissions/a386f005-c2b8-45cb-a88c-417e402eedac

import Mathlib

theorem solution (R : Type*) [CommRing R] [IsNoetherianRing R] : ringKrullDim (Polynomial R) = ringKrullDim R + 1 :=
  Polynomial.ringKrullDim_of_isNoetherianRing
