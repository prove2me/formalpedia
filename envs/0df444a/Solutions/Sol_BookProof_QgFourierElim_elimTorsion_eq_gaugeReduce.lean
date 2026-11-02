-- Prove2me | solution 1 for BookProof.QgFourierElim.elimTorsion_eq_gaugeReduce
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-02T02:17:06.988769+00:00
-- url     : https://prove2.me/submissions/0c395f98-80ef-4a47-8a91-27d0eea8022d

-- Generated from ChapterQgFourierElimination.lean — solution of BookProof.QgFourierElim.elimTorsion_eq_gaugeReduce
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
import Definitions.Def_ChapterQgBrstDerivativeGaugeV2
open BookProof.QgFourierElim




open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL
open BookProof.QgBrstDerivativeGauge

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (k : Mom) (mu nu i : Fin 3) (x : CMode) :
    elimTorsion k mu nu i x = gaugeReduce (extTorsionCoef k mu nu i) x := by

  rw [elimTorsion_eq_torsionCoef, gaugeReduce_extTorsionCoef]
