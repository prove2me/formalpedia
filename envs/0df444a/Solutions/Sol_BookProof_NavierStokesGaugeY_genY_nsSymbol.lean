-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genY_nsSymbol
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:17:17.886025+00:00
-- url     : https://prove2.me/submissions/88e014f5-6b1d-4d10-9fc2-60d44b5559aa

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genY_nsSymbol
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow


theorem solution (nu : ℂ) (i j : Fin 3) : genY j (nsSymbol nu i) = 0 := by
  simp [genY, nsSymbol, uField, pderiv_X, Pi.single_apply, Fin.sum_univ_three]
  fin_cases j <;> simp <;> ring

