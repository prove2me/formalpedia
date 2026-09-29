-- Prove2me | solution 1 for FamousTheorems.bezout_identity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:15:02.720145+00:00
-- url     : https://prove2.me/submissions/0bcd7380-fe32-4430-a43d-cf6777372652

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [GCDMonoid R] (a b : R) : ∃ x y, gcd a b = a * x + b * y :=
  exists_gcd_eq_mul_add_mul a b
