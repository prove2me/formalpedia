-- Prove2me | solution 1 for FamousTheorems.weierstrass_p_differential_equation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:24:04.722053+00:00
-- url     : https://prove2.me/submissions/0ecc0fa0-e11b-4a87-be6d-ddcfc6a23b87

import Mathlib

theorem solution (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    L.derivWeierstrassP z ^ 2 = 4 * L.weierstrassP z ^ 3 - L.g₂ * L.weierstrassP z - L.g₃ :=
  L.derivWeierstrassP_sq z hz
