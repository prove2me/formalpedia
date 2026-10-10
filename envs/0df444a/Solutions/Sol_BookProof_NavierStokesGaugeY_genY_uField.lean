-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genY_uField
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:07:46.869974+00:00
-- url     : https://prove2.me/submissions/2da2c24d-68ce-4be9-a076-14038d7eb6d8

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.genY_uField
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow


private theorem genY_apply (j : Fin 3) (p : NSAlg) :
    genY j p = pderiv (NSVar.y j) p - ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.u i) p := by
  simp [genY]

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) : genY j (uField i) = 0 := by

  simp [genY_apply, uField, pderiv_X, Pi.single_apply, Finset.sum_ite_eq', apply_ite]
