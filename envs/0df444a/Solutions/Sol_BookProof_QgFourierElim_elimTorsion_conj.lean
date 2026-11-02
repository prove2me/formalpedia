-- Prove2me | solution 1 for BookProof.QgFourierElim.elimTorsion_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-01T21:36:19.002197+00:00
-- url     : https://prove2.me/submissions/c164aacd-ce4e-4575-9a06-ecb8478a38fc

-- Generated from ChapterQgFourierElimination.lean — solution of BookProof.QgFourierElim.elimTorsion_conj
import Mathlib
import Definitions.Def_ChapterQgFourierElimination
import Theorems.Thm_BookProof_QgFourierElim_elimTorsion_eq_torsionCoef
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterA4
open BookProof.QgFourierElim




open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (k : Mom) (mu nu i : Fin 3) (z : CMode) :
    (starRingEnd ℂ) (elimTorsion k mu nu i z) = elimTorsion k mu nu i z := by

  rw [elimTorsion_eq_torsionCoef]
  split
  · exact torsionCoef_conj k mu nu i z
  · exact map_zero _
