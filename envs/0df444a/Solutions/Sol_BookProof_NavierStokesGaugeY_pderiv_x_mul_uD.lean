-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.pderiv_x_mul_uD
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:02.938347+00:00
-- url     : https://prove2.me/submissions/fbec2a67-404d-433e-9963-10aebd42c5e4

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.pderiv_x_mul_uD
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (m i j : Fin 3) (q : NSAlg) :
    pderiv (NSVar.x m) (X (NSVar.uD i j) * q) = X (NSVar.uD i j) * pderiv (NSVar.x m) q := by

  rw [pderiv_mul, pderiv_X_of_ne (by simp)]; ring
