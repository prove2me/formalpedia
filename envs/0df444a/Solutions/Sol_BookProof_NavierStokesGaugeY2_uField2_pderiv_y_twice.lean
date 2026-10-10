-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.uField2_pderiv_y_twice
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:23.177778+00:00
-- url     : https://prove2.me/submissions/583ad89a-75e5-4b9d-b546-256a76d1fc96

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.uField2_pderiv_y_twice
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Theorems.Thm_BookProof_NavierStokesGaugeY2_uField2_pderiv_y
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) :
    pderiv (NSVar.y j) (pderiv (NSVar.y j) (uField2 i)) = X (NSVar.uL i) := by

  rw [uField2_pderiv_y, uDField, map_add, pderiv_mul]
  simp [pderiv_X]
