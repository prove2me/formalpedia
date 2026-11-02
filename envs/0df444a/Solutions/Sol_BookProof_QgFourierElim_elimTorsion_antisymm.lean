-- Prove2me | solution 1 for BookProof.QgFourierElim.elimTorsion_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-01T21:36:10.92219+00:00
-- url     : https://prove2.me/submissions/be8cc99d-3c6a-44be-b788-fdb36a5ecb21

-- Generated from ChapterQgFourierElimination.lean — solution of BookProof.QgFourierElim.elimTorsion_antisymm
import Mathlib
import Definitions.Def_ChapterQgFourierElimination
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
    elimTorsion k nu mu i z = -elimTorsion k mu nu i z := by

  simp only [elimTorsion]
  ring
