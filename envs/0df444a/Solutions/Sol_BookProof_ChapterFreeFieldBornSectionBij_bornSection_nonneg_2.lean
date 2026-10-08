-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBornSectionBij.bornSection_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:51:10.708305+00:00
-- url     : https://prove2.me/submissions/0096e2d2-909e-4fff-a346-a657928368c7

import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSectionBij

open BookProof.ChapterFreeFieldBornSectionBij MeasureTheory BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj in
theorem solution {n : ℕ} (p : Fin n → ℝ) : bornSection p ∈ nonnegOrthant n := by
  intro k
  exact Real.sqrt_nonneg _
