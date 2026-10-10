-- Prove2me | solution 1 for BookProof.ChapterPauliGrover.pauliX_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:35.73799+00:00
-- url     : https://prove2.me/submissions/58d10b84-7ff7-4910-a073-4eff75684cab

-- Generated from ChapterPauliGrover.lean — solution of BookProof.ChapterPauliGrover.pauliX_conjTranspose
import Mathlib
import Definitions.Def_ChapterPauliGrover
import Definitions.Def_ChapterConditional
open BookProof.ChapterPauliGrover



open scoped BigOperators Matrix ComplexConjugate
open Matrix
open BookProof.ChapterConditional

set_option maxHeartbeats 1000000 in
theorem solution : pauliX.conjTranspose = pauliX := by

  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]
