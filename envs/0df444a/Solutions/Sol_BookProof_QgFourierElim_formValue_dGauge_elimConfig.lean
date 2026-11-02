-- Prove2me | solution 1 for BookProof.QgFourierElim.formValue_dGauge_elimConfig
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-01T18:43:28.334298+00:00
-- url     : https://prove2.me/submissions/635aa6f0-9d9e-43ec-b447-0c2c9f57e019

-- Generated from ChapterQgFourierElimination.lean — solution of BookProof.QgFourierElim.formValue_dGauge_elimConfig
import Mathlib
import Definitions.Def_ChapterQgFourierElimination
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterQgFourierElimForms
open BookProof.QgFourierElim




open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (mu nu i : Fin 3) :
    formValue k (dGaugeF mu nu i) (elimConfig k z) = 0 := by

  rw [formValue_dGauge, elimConfig_d, elimConfig_e, sub_self]
