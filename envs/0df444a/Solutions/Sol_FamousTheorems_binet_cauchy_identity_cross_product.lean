-- Prove2me | solution 1 for FamousTheorems.binet_cauchy_identity_cross_product
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:17:58.335346+00:00
-- url     : https://prove2.me/submissions/975d3716-7bc0-4343-94e3-ecd6fb971091

import Mathlib

theorem solution {R : Type*} [CommRing R] (u v w x : Fin 3 → R) :
    dotProduct (crossProduct u v) (crossProduct w x) =
      dotProduct u w * dotProduct v x - dotProduct u x * dotProduct v w :=
  cross_dot_cross u v w x
