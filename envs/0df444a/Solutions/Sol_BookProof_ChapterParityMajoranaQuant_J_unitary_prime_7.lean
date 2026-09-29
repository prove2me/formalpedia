-- Prove2me | solution 7 for BookProof.ChapterParityMajoranaQuant.J_unitary_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T08:20:20.00762+00:00
-- url     : https://prove2.me/submissions/8be099b9-741c-4c49-8dc8-28a7da825faa

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
