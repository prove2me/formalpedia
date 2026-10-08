-- Prove2me | solution 1 for BookProof.ChapterA3.paulisigma_herm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:05:06.529975+00:00
-- url     : https://prove2.me/submissions/845ba99f-6dc6-4aa5-95c4-bdb66eef105d

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.paulisigma_herm
import Mathlib
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) : (pauliσ μ)ᴴ = pauliσ μ := by

  fin_cases μ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauliσ, Matrix.conjTranspose_apply])
