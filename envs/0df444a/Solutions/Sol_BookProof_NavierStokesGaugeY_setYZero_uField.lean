-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY.setYZero_uField
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:15:22.280703+00:00
-- url     : https://prove2.me/submissions/5eeee8e6-f87b-4b50-b930-077ab0a7d307

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.setYZero_uField
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow


theorem solution (i : Fin 3) : setYZero (uField i) = X (NSVar.u i) := by
  simp [setYZero, uField]

