-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genX_uField
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:08.05408+00:00
-- url     : https://prove2.me/submissions/253425e9-0958-4b09-83ac-285451021bfc

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.genX_uField
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Theorems.Thm_BookProof_NavierStokesGaugeY_uField_pderiv_x
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (i j : Fin 3) : genX j (uField i) = 0 := uField_pderiv_x i j
