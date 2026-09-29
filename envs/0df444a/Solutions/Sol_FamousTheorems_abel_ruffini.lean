-- Prove2me | solution 1 for FamousTheorems.abel_ruffini
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:17:24.655161+00:00
-- url     : https://prove2.me/submissions/02fd4fc0-b71a-4ec1-941f-9ed9d0bb97af

import Mathlib

theorem solution {F E : Type*} [Field F] [Field E] [Algebra F E] {x : E} (hx : x ∈ solvableByRad F E) {q : Polynomial F}
    (hq : Irreducible q) (hqx : Polynomial.aeval x q = 0) : Group.IsSolvable q.Gal :=
  isSolvable_gal_of_irreducible hx hq hqx
