-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.genY_uField2_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:08:35.262656+00:00
-- url     : https://prove2.me/submissions/58962ead-7f19-4e2f-b35f-c3f739fd0de2

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.genY_uField2_ne_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Theorems.Thm_BookProof_NavierStokesGaugeY2_genY_uField2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) : genY j (uField2 i) ≠ 0 := by

  rw [genY_uField2]
  exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)
