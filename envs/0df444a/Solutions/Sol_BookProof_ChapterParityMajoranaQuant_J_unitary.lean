-- Prove2me | solution 1 for BookProof.ChapterParityMajoranaQuant.J_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:17:17.450653+00:00
-- url     : https://prove2.me/submissions/8b4d87a9-7980-4f6f-9658-1f7e135748ca

-- Generated from ChapterParityMajoranaQuant.lean — solution of BookProof.ChapterParityMajoranaQuant.J_unitary
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant











open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

set_option maxHeartbeats 1000000 in
theorem solution (hJ2 : J * J = -1) (hskew : Jᴴ = -J) : Jᴴ * J = 1 := by

  rw [hskew, neg_mul, hJ2, neg_neg]
