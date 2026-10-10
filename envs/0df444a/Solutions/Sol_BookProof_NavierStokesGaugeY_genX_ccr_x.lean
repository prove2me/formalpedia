-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genX_ccr_x
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:06.79971+00:00
-- url     : https://prove2.me/submissions/a26d3b7a-22ff-4568-8644-a4b12b8a6087

-- Generated from ChapterNavierStokesGaugeY.lean — solution of BookProof.NavierStokesGaugeY.genX_ccr_x
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
import Theorems.Thm_BookProof_NavierStokesFlow_ccr_field
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY




open MvPolynomial BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (j k : Fin 3) (p : NSAlg) :
    genX j (X (NSVar.x k) * p) - X (NSVar.x k) * genX j p
      = if NSVar.x j = NSVar.x k then p else 0 := ccr_field _ _ p
