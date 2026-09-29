-- Prove2me | solution 1 for FamousTheorems.cross_product_jacobi_identity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:41:29.917311+00:00
-- url     : https://prove2.me/submissions/d64204af-27be-4739-9cd0-246c3a548349

import Mathlib

theorem solution {R : Type*} [CommRing R] (u v w : Fin 3 → R) :
    crossProduct u (crossProduct v w) + crossProduct v (crossProduct w u) + crossProduct w (crossProduct u v) = 0 :=
  jacobi_cross u v w
