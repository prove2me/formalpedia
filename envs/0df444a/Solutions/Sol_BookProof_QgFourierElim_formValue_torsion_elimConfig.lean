-- Prove2me | solution 1 for BookProof.QgFourierElim.formValue_torsion_elimConfig
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-01T18:43:36.27794+00:00
-- url     : https://prove2.me/submissions/dbe1cf18-3f91-42f2-a9c2-dc9c472198fa

-- Generated from ChapterQgFourierElimination.lean — solution of BookProof.QgFourierElim.formValue_torsion_elimConfig
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
    formValue k (torsionF mu nu i) (elimConfig k z)
      = Complex.I * (((k mu : ℤ) : ℂ) * z (nu, i) - ((k nu : ℤ) : ℂ) * z (mu, i)) := by

  rw [formValue_torsion, elimConfig_d, elimConfig_d]
  ring
