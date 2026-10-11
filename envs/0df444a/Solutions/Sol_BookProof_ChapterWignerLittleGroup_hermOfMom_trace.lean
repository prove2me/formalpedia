-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.hermOfMom_trace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:59:57.522698+00:00
-- url     : https://prove2.me/submissions/a52d9fae-d86f-41c8-9cbf-64dd6d13581f

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.hermOfMom_trace
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin 4 → ℝ) :
    (hermOfMom p).trace = ((2 * p 0 : ℝ) : ℂ) := by

  simp [hermOfMom, Matrix.trace_fin_two_of]
  ring
