-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.ext_apply
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:13:55.203873+00:00
-- url     : https://prove2.me/submissions/5ceaba4a-684e-482b-ad6d-e6d58240bc68

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
    (d : CoreData F) (x : d.C.dom) : d.ext x = d.extCLM (d.C.op x + (x : F)) := by
  rfl
