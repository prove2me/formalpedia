-- Prove2me | solution 1 for BookProof.ChapterPauliGrover.pauliGrover_cond_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:42.220115+00:00
-- url     : https://prove2.me/submissions/40d40b9e-e63a-4677-b4ac-b23b4875627c

-- Generated from ChapterPauliGrover.lean — solution of BookProof.ChapterPauliGrover.pauliGrover_cond_one
import Mathlib
import Definitions.Def_ChapterPauliGrover
import Theorems.Thm_BookProof_ChapterPauliGrover_pauliGrover_joint_one
import Theorems.Thm_BookProof_ChapterPauliGrover_pauliGrover_marg_one
import Definitions.Def_ChapterConditional
open BookProof.ChapterPauliGrover



open scoped BigOperators Matrix ComplexConjugate
open Matrix
open BookProof.ChapterConditional

set_option maxHeartbeats 1000000 in
theorem solution : pCond pauliX (0 : Fin 2) 1 = 1 := by

  rw [pCond, pauliGrover_joint_one, pauliGrover_marg_one]
  norm_num
