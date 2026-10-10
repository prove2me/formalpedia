-- Prove2me | solution 1 for BookProof.ChapterPauliGrover.pauliX_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:37.939394+00:00
-- url     : https://prove2.me/submissions/d5c4cfae-dfd5-4bf5-b7ff-36ba9e841be6

-- Generated from ChapterPauliGrover.lean — solution of BookProof.ChapterPauliGrover.pauliX_unitary
import Mathlib
import Definitions.Def_ChapterPauliGrover
import Theorems.Thm_BookProof_ChapterPauliGrover_pauliX_conjTranspose
import Theorems.Thm_BookProof_ChapterPauliGrover_pauliX_sq
import Definitions.Def_ChapterConditional
open BookProof.ChapterPauliGrover



open scoped BigOperators Matrix ComplexConjugate
open Matrix
open BookProof.ChapterConditional

set_option maxHeartbeats 1000000 in
theorem solution : pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by

  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, pauliX_conjTranspose]
  exact pauliX_sq
