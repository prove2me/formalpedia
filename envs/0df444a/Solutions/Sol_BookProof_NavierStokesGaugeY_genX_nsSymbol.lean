-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.genX_nsSymbol
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:17:05.112765+00:00
-- url     : https://prove2.me/submissions/517d2d94-3885-444c-b7cd-2af27a1d4839

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genX_nsSymbol
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow


theorem solution (nu : ℂ) (i j : Fin 3) : genX j (nsSymbol nu i) = 0 := by
  simp [genX, nsSymbol, uField, pderiv_X]

