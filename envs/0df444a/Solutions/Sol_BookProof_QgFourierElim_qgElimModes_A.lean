-- Prove2me | solution 1 for BookProof.QgFourierElim.qgElimModes_A
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-01T21:36:31.046949+00:00
-- url     : https://prove2.me/submissions/5bed5868-f9bb-4656-bf6f-f37fc89b5ed5

-- Generated from ChapterQgFourierElimination.lean — solution of BookProof.QgFourierElim.qgElimModes_A
import Mathlib
import Definitions.Def_ChapterQgFourierElimination
import Theorems.Thm_BookProof_QgFourierElim_elimGram_funext
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
theorem solution (g : ℝ) : (qgElimModes g).A = elimGram := elimGram_funext.symm
