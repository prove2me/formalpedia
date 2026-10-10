-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.pderiv_u_mul_uD
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:00.046988+00:00
-- url     : https://prove2.me/submissions/9e93f8ed-c3c6-42e5-bbef-016e689ab0ff

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.pderiv_u_mul_uD
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (m i j : Fin 3) (q : NSAlg) :
    pderiv (NSVar.u m) (X (NSVar.uD i j) * q) = X (NSVar.uD i j) * pderiv (NSVar.u m) q := by

  rw [pderiv_mul, pderiv_X_of_ne (by simp)]; ring
