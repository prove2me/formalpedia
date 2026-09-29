-- Prove2me | solution 1 for FamousTheorems.cstar_algebra_increasing_approximate_unit_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:42:31.846352+00:00
-- url     : https://prove2.me/submissions/ff8d0997-76b2-4ef5-a63f-95b98d3adbf8

import Mathlib

theorem solution (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    (CStarAlgebra.approximateUnit A).IsIncreasingApproximateUnit :=
  CStarAlgebra.increasingApproximateUnit A
