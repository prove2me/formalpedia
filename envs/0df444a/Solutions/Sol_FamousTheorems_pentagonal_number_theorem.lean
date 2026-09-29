-- Prove2me | solution 1 for FamousTheorems.pentagonal_number_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:15:55.900873+00:00
-- url     : https://prove2.me/submissions/15b1a20a-529a-4206-b8c7-ab7d2d57493e

import Mathlib

open scoped PowerSeries.WithPiTopology

theorem solution (R : Type*) [CommRing R] [TopologicalSpace R] :
    HasProd (fun n : ℕ => (1 - PowerSeries.X ^ (n + 1) : PowerSeries R)) (PowerSeries.pentagonalSeries R) :=
  PowerSeries.WithPiTopology.hasProd_one_sub_X_pow R
