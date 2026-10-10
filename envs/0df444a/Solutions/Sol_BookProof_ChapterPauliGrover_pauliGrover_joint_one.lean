-- Prove2me | solution 1 for BookProof.ChapterPauliGrover.pauliGrover_joint_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:39.969917+00:00
-- url     : https://prove2.me/submissions/0abe3b0a-ffbe-49e4-8766-c106c2536ec0

-- Generated from ChapterPauliGrover.lean — solution of BookProof.ChapterPauliGrover.pauliGrover_joint_one
import Mathlib
import Definitions.Def_ChapterPauliGrover
import Definitions.Def_ChapterConditional
open BookProof.ChapterPauliGrover



open scoped BigOperators Matrix ComplexConjugate
open Matrix
open BookProof.ChapterConditional

set_option maxHeartbeats 1000000 in
theorem solution : pJoint pauliX (0 : Fin 2) 1 = 1 := by

  simp [pJoint, pauliX]
