-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBornCont.isCompact_stdSimplex_of_born
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T16:53:13.567729+00:00
-- url     : https://prove2.me/submissions/986fdb4c-7011-4abf-85ce-e17a997a6e9f

import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont

set_option autoImplicit false

open BookProof.ChapterFreeFieldBornCont MeasureTheory BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj in
theorem solution {n : ℕ} :
    IsCompact (stdSimplex ℝ (Fin n)) := by
  exact isCompact_stdSimplex ℝ (Fin n)
