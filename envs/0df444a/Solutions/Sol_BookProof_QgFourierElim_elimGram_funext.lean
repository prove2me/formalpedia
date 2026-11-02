-- Prove2me | solution 1 for BookProof.QgFourierElim.elimGram_funext
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-01T21:36:27.189721+00:00
-- url     : https://prove2.me/submissions/ca542684-fd0c-4ed7-aaf5-ed3e09030852

-- Generated from ChapterQgFourierElimination.lean — solution of BookProof.QgFourierElim.elimGram_funext
import Mathlib
import Definitions.Def_ChapterQgFourierElimination
import Theorems.Thm_BookProof_QgFourierElim_elimGram_eq_contTorsionGram
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
theorem solution : elimGram = contTorsionGram := by

  funext x y
  exact elimGram_eq_contTorsionGram x y
