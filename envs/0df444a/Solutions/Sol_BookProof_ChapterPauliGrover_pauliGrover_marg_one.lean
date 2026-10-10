-- Prove2me | solution 1 for BookProof.ChapterPauliGrover.pauliGrover_marg_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:41.037741+00:00
-- url     : https://prove2.me/submissions/ddea289a-0073-4b95-b9c7-2de6bc4665fd

-- Generated from ChapterPauliGrover.lean — solution of BookProof.ChapterPauliGrover.pauliGrover_marg_one
import Mathlib
import Definitions.Def_ChapterPauliGrover
import Definitions.Def_ChapterConditional
open BookProof.ChapterPauliGrover



open scoped BigOperators Matrix ComplexConjugate
open Matrix
open BookProof.ChapterConditional

set_option maxHeartbeats 1000000 in
theorem solution : pMarg pauliX (0 : Fin 2) = 1 := by

  simp [pMarg, pauliX, Fin.sum_univ_two]
