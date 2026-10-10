-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.uField_pderiv_x
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:05.648836+00:00
-- url     : https://prove2.me/submissions/f6561cfd-0844-4c53-82d6-c4cab7c78098

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.uField_pderiv_x
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) : pderiv (NSVar.x j) (uField i) = 0 := by

  simp [uField, pderiv_X]
