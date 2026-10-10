-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genX_ccr_y
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:06:20.95698+00:00
-- url     : https://prove2.me/submissions/27a134ba-37f4-4842-8764-cf56f310099e

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.genX_ccr_y
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow


@[simp] private theorem genX_apply (j : Fin 3) (p : NSAlg) : genX j p = pderiv (NSVar.x j) p := rfl

set_option maxHeartbeats 1000000 in
theorem solution (j k : Fin 3) (p : NSAlg) :
    genX j (X (NSVar.y k) * p) - X (NSVar.y k) * genX j p = 0 := by

  rw [genX_apply, genX_apply, pderiv_mul, pderiv_X_of_ne (by simp)]; ring
