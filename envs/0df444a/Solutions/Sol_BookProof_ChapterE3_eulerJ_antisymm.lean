-- Prove2me | solution 1 for BookProof.ChapterE3.eulerJ_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:31:08.215464+00:00
-- url     : https://prove2.me/submissions/0336965a-fb47-4988-9a00-a551dabfdd42

-- Generated from ChapterE3.lean — solution of BookProof.ChapterE3.eulerJ_antisymm
import Mathlib
import Definitions.Def_ChapterE3
open BookProof.ChapterE3



open scoped Matrix BigOperators


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (l w : Fin n → ℝ) :
    (eulerJ l w)ᵀ = - eulerJ l w := by

  ext i j; simp [eulerJ];
  simp [ Matrix.vecMulVec, mul_comm ]
