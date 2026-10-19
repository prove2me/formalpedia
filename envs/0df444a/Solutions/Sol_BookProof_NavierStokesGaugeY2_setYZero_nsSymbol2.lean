-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.setYZero_nsSymbol2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:19:51.864822+00:00
-- url     : https://prove2.me/submissions/3b049f05-97be-482b-947f-0cd020817fd6

import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.setYZero_nsSymbol2
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY


theorem solution (nu : ℂ) (i : Fin 3) :
    setYZero (nsSymbol2 nu i) = nsSymbolPoint nu i := by
  simp [setYZero, nsSymbol2, nsSymbolPoint, uField2, uDField]

