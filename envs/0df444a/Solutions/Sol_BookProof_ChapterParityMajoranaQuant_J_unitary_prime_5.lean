-- Prove2me | solution 5 for BookProof.ChapterParityMajoranaQuant.J_unitary_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T08:19:14.836741+00:00
-- url     : https://prove2.me/submissions/00488791-0334-45a3-ae62-b4e643c995b1

-- Generated from ChapterParityMajoranaQuant.lean — solution of BookProof.ChapterParityMajoranaQuant.J_unitary_prime
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant











open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

set_option maxHeartbeats 1000000 in
theorem solution (hJ2 : J * J = -1) (hskew : Jᴴ = -J) : J * Jᴴ = 1 := by

  rw [hskew, mul_neg, hJ2, neg_neg]
