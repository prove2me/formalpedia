-- Prove2me | solution 1 for BookProof.ChapterGleasonPureMixed.halfI_not_pure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:47:55.139993+00:00
-- url     : https://prove2.me/submissions/53d3290b-0c46-4181-96b1-9ba3c5d86f50

-- Generated from ChapterGleasonPureMixed.lean — solution of BookProof.ChapterGleasonPureMixed.halfI_not_pure
import Mathlib
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterGleasonPureMixed



open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ IsPureState ((1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by

  rintro ⟨-, hidem, -⟩
  have := congrFun (congrFun hidem 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this
