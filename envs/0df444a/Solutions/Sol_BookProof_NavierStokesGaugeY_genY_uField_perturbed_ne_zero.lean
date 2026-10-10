-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genY_uField_perturbed_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:08:21.318695+00:00
-- url     : https://prove2.me/submissions/b8d188d7-a692-4ab8-a279-8a8ed3ccba12

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.genY_uField_perturbed_ne_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Theorems.Thm_BookProof_NavierStokesGaugeY_genY_uField_perturbed
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) (c : ℂ) (hc : c ≠ 0) :
    genY j (uField i + C c * X (NSVar.y j)) ≠ 0 := by

  rw [genY_uField_perturbed]
  simpa using hc
