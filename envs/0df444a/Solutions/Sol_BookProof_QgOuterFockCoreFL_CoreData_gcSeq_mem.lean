-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.gcSeq_mem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:32:11.806577+00:00
-- url     : https://prove2.me/submissions/8f87c132-6e6f-49e2-910e-7aee58631640

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
    (d : CoreData F) (x : d.C.dom) (k : ℕ) :
    ((d.gcSeq x k : d.C.dom) : F) ∈ d.C₀ := by
  exact (d.gc.approx x (1 / (k + 1)) (by positivity)).choose_spec.1
