-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.uField_pderiv_y
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:04.224911+00:00
-- url     : https://prove2.me/submissions/82fb4ff2-1b45-4273-a35b-a2bd59dd8596

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.uField_pderiv_y
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) :
    pderiv (NSVar.y j) (uField i) = X (NSVar.uD i j) := by

  simp [uField, pderiv_X, Pi.single_apply, Finset.sum_ite_eq', apply_ite]
