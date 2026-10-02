-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.coreRange_denseRange
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:50:17.405197+00:00
-- url     : https://prove2.me/submissions/9c04da16-39e0-451d-92c3-c49e0b93c194

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

open BookProof.QgOuterFockCoreFL BookProof.QgOuterFockCoreFL.CoreData BookProof.FarisLavine BookProof.DirectSumEsa BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.YangMillsFriedrichs BookProof.EsaClosure BookProof.QgHermiteOscillator BookProof.HermiteProductCore Filter Topology in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (d : CoreData F) : DenseRange (d.coreRange.subtypeL) := by
  rw [Metric.denseRange_iff]
  intro f r hr
  obtain ⟨x, hx⟩ := d.C.surj f
  obtain ⟨y, hyC, h1, h2⟩ := d.gc.approx x (r / 2) (by linarith)
  refine ⟨⟨d.coreShift ⟨(y : F), hyC⟩, ⟨⟨(y : F), hyC⟩, rfl⟩⟩, ?_⟩
  have hyy : (⟨(y : F), d.gc.le hyC⟩ : d.C.dom) = y := rfl
  show dist f (d.coreShift ⟨(y : F), hyC⟩) < r
  rw [coreShift_apply, hyy, ← hx, dist_eq_norm]
  have : d.C.op x + (x : F) - (d.C.op y + (y : F))
      = -((d.C.op y - d.C.op x) + ((y : F) - (x : F))) := by abel
  rw [this, norm_neg]
  calc ‖(d.C.op y - d.C.op x) + ((y : F) - (x : F))‖
      ≤ ‖d.C.op y - d.C.op x‖ + ‖(y : F) - (x : F)‖ := norm_add_le _ _
    _ < r := by linarith
