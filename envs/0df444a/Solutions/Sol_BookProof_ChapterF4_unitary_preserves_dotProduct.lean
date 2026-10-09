-- Prove2me | solution 1 for BookProof.ChapterF4.unitary_preserves_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:01:45.406954+00:00
-- url     : https://prove2.me/submissions/fdbb95e6-4cad-401c-b448-39e0c7f43580

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.unitary_preserves_dotProduct
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ * U = 1) (x y : Fin n → ℂ) :
    star (U.mulVec x) ⬝ᵥ U.mulVec y = star x ⬝ᵥ y := by

  -- By the properties of the Hermitian transpose, we have:
  have h_star_mul : star (U *ᵥ x) = (star x) ᵥ* Uᴴ := by
    have h_conj : ∀ (v : Fin n → ℂ), star (U *ᵥ v) = (star v) ᵥ* Uᴴ := by
      intro v; ext i; simp [ Matrix.mulVec, dotProduct ] ;
      simp [ Matrix.vecMul, dotProduct, mul_comm ]
    exact h_conj x;
  simp_all ;
  simp [ Matrix.dotProduct_mulVec, hU ]
