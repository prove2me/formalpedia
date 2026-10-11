-- Prove2me | solution 1 for BookProof.NavierStokesEulerian.eulerian_momentum_constraint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:22.733214+00:00
-- url     : https://prove2.me/submissions/11c066db-0a9a-4f83-bf3e-6148d57bd7a7

-- Generated from ChapterNavierStokesEulerian.lean — solution of BookProof.NavierStokesEulerian.eulerian_momentum_constraint
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Theorems.Thm_BookProof_NavierStokesFlow_ccr_field
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesEulerian




open BookProof.NavierStokesFlow Matrix

set_option maxHeartbeats 1000000 in
theorem solution (j k : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    (MvPolynomial.pderiv k) (MvPolynomial.X j * p)
      - MvPolynomial.X j * (MvPolynomial.pderiv k) p = (if k = j then p else 0) := ccr_field k j p
