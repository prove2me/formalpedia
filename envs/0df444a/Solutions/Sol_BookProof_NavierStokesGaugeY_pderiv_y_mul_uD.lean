-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.pderiv_y_mul_uD
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:01.559626+00:00
-- url     : https://prove2.me/submissions/9f881546-9f98-4e34-8dc4-511762eea932

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.pderiv_y_mul_uD
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (m i j : Fin 3) (q : NSAlg) :
    pderiv (NSVar.y m) (X (NSVar.uD i j) * q) = X (NSVar.uD i j) * pderiv (NSVar.y m) q := by

  rw [pderiv_mul, pderiv_X_of_ne (by simp)]; ring
