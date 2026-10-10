-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed_ne_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:08:58.951557+00:00
-- url     : https://prove2.me/submissions/03c4ef66-eb7c-4c25-b03e-71cd0dee057f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed_ne_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Theorems.Thm_BookProof_NavierStokesGaugeY2_genY2_uField2_perturbed
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) (c : ℂ) (hc : c ≠ 0) :
    genY2 j (uField2 i + C c * (X (NSVar.y j) * X (NSVar.y j))) ≠ 0 := by

  rw [genY2_uField2_perturbed]
  refine mul_ne_zero ?_ (mul_ne_zero two_ne_zero (X_ne_zero _))
  simpa using hc
