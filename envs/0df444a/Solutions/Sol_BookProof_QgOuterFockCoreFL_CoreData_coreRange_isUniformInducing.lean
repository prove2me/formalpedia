-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.coreRange_isUniformInducing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T02:55:32.625965+00:00
-- url     : https://prove2.me/submissions/2ec9d8d9-f7a5-4391-aa7f-61bb21e6aee9

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockCoreFL

set_option autoImplicit false

universe u_1

open BookProof.QgOuterFockCoreFL BookProof.QgOuterFockCoreFL.CoreData BookProof.FarisLavine BookProof.DirectSumEsa BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.YangMillsFriedrichs BookProof.EsaClosure BookProof.QgHermiteOscillator BookProof.HermiteProductCore Filter Topology in
theorem solution {F : Type u_1} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (d : CoreData F) : IsUniformInducing (d.coreRange.subtypeL) := by
  exact isUniformEmbedding_subtype_val.isUniformInducing
