-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.coreRange_dense
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:35:07.008847+00:00
-- url     : https://prove2.me/submissions/64b5899f-a436-41a7-8d06-aa064678bbe5

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
    (d : CoreData F) : Dense ((d.coreRange : Submodule ℂ F) : Set F) := by
  rw [Metric.dense_iff]
  intro f r hr
  obtain ⟨x, hx⟩ := d.C.surj f
  obtain ⟨y, hyC, hy1, hy2⟩ := d.gc.approx x (r / 2) (by linarith)
  refine ⟨d.coreShift ⟨(y : F), hyC⟩, ?_, LinearMap.mem_range_self _ _⟩
  rw [Metric.mem_ball, dist_eq_norm, coreShift_apply]
  have hyy : (⟨(y : F), d.gc.le hyC⟩ : d.C.dom) = y := Subtype.ext rfl
  rw [hyy, ← hx]
  calc ‖d.C.op y + (y : F) - (d.C.op x + (x : F))‖
      = ‖(d.C.op y - d.C.op x) + ((y : F) - (x : F))‖ := by congr 1; abel
    _ ≤ ‖d.C.op y - d.C.op x‖ + ‖(y : F) - (x : F)‖ := norm_add_le _ _
    _ < r := by linarith
