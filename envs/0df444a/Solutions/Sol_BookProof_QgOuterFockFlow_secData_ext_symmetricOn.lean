-- Prove2me | solution 1 for BookProof.QgOuterFockFlow.secData_ext_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T10:53:17.954657+00:00
-- url     : https://prove2.me/submissions/cebb5afe-31e0-4fae-9fd3-701246e01418

-- Generated from ChapterQgOuterFockFlow.lean — solution of BookProof.QgOuterFockFlow.secData_ext_symmetricOn
import Mathlib
import Definitions.Def_ChapterQgOuterFockFlow
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_symmetricOn
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockCoreFL




open Filter Topology
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData

noncomputable section

variable {ι : Type*} (W : WallPot) (Q : QgModeData ι)

set_option maxHeartbeats 1000000 in
theorem solution :
    SymmetricOn (secN W Q).dom (secData W Q).ext := (secData W Q).ext_symmetricOn (secHam_symmetricOn W Q)
