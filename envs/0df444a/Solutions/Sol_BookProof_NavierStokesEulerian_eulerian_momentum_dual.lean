-- Prove2me | solution 1 for BookProof.NavierStokesEulerian.eulerian_momentum_dual
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:24.579306+00:00
-- url     : https://prove2.me/submissions/e4c6eb3a-cd2f-4bfc-953f-5829823012ad

-- Generated from ChapterNavierStokesEulerian.lean — solution of BookProof.NavierStokesEulerian.eulerian_momentum_dual
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesEulerian




open BookProof.NavierStokesFlow Matrix

set_option maxHeartbeats 1000000 in
theorem solution (i j k l : Fin 3) :
    (MvPolynomial.pderiv (i, j)) (MvPolynomial.X (k, l) : MvPolynomial (Fin 3 × Fin 3) ℂ)
      = if i = k ∧ j = l then 1 else 0 := by

  rw [MvPolynomial.pderiv_X]
  simp [Prod.ext_iff, Pi.single_apply, eq_comm]
