-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.norm_resolvedCLM_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:40:48.244262+00:00
-- url     : https://prove2.me/submissions/cb961bc9-ff4b-410d-bcd2-eb0aaebe450d

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockCoreFL

set_option autoImplicit false

open BookProof.QgOuterFockCoreFL BookProof.QgOuterFockCoreFL.CoreData in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (d : CoreData F) : ‖d.resolvedCLM‖ ≤ d.K := by
  unfold BookProof.QgOuterFockCoreFL.CoreData.resolvedCLM
  exact LinearMap.mkContinuous_norm_le _ d.hK _

