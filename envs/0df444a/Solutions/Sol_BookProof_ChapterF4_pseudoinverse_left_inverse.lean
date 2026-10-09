-- Prove2me | solution 1 for BookProof.ChapterF4.pseudoinverse_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:01:59.261197+00:00
-- url     : https://prove2.me/submissions/ca1a5d00-f186-4089-bb2f-956166006c49

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.pseudoinverse_left_inverse
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

set_option maxHeartbeats 1000000 in
theorem solution {m n : ℕ} (Φ : Matrix (Fin m) (Fin n) ℂ)
    (h : IsUnit (Φᴴ * Φ).det) :
    ((Φᴴ * Φ)⁻¹ * Φᴴ) * Φ = 1 := by

  simp_all [ Matrix.mul_assoc ]
