-- Prove2me | solution 1 for BookProof.ChapterPauliGrover.pauliX_rotates
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:38.962548+00:00
-- url     : https://prove2.me/submissions/7385e849-699d-4c30-b970-f14dea40c1b7

-- Generated from ChapterPauliGrover.lean — solution of BookProof.ChapterPauliGrover.pauliX_rotates
import Mathlib
import Definitions.Def_ChapterPauliGrover
import Definitions.Def_ChapterConditional
open BookProof.ChapterPauliGrover



open scoped BigOperators Matrix ComplexConjugate
open Matrix
open BookProof.ChapterConditional

set_option maxHeartbeats 1000000 in
theorem solution : pauliX 1 0 = 1 ∧ pauliX 0 0 = 0 := by

  constructor <;> simp [pauliX]
