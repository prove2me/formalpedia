-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.coreEquiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:02:15.281014+00:00
-- url     : https://prove2.me/submissions/69abe0bb-166a-4931-ad14-06d372edbc2d

import Mathlib
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteQuadraticEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQgOuterFockCoreFL

set_option autoImplicit false

open BookProof.HermiteProductCore BookProof.NavierStokesFlow.DifferentialL2 in
theorem solution {D : ℕ} (p : MvPolynomial (Fin D) ℂ) :
    BookProof.NavierStokesFlow.DifferentialL2.coreEquiv p
      = (⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := D)) := by
  apply Subtype.ext
  rfl
