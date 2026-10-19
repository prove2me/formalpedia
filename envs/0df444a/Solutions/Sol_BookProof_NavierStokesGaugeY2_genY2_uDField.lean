-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.genY2_uDField
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:24:12.797767+00:00
-- url     : https://prove2.me/submissions/6cd9bc89-1547-4021-9b31-cf2908e34bf1

import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.genY2_uDField
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY


theorem solution (i j k : Fin 3) : genY2 j (uDField i k) = 0 := by
  simp [genY2, uDField, pderiv_X, Pi.single_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp

