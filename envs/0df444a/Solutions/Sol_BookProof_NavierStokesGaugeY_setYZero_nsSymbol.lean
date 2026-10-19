-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.setYZero_nsSymbol
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:15:35.38711+00:00
-- url     : https://prove2.me/submissions/a540d670-d1a7-4c08-8a1e-f624603cb1f8

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.setYZero_nsSymbol
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow


theorem solution (nu : ℂ) (i : Fin 3) :
    setYZero (nsSymbol nu i) = nsSymbolPoint nu i := by
  simp [setYZero, nsSymbol, nsSymbolPoint, uField]

