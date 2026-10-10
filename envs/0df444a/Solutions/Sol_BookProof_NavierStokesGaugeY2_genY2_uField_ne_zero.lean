-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.genY2_uField_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:08:57.468837+00:00
-- url     : https://prove2.me/submissions/707c967e-a4da-4a82-9bb0-d92bace60dc9

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.genY2_uField_ne_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Theorems.Thm_BookProof_NavierStokesGaugeY2_genY2_uField
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) : genY2 j (uField i) ≠ 0 := by

  rw [genY2_uField, neg_ne_zero]
  exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)
