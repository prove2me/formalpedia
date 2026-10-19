-- Prove2me | solution 1 for CompactnessConjecture.symmetricQuadratic_no_three_independent_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/9ddcd10b-7eaa-41d8-b0ad-9132539f2151

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symmetricQuadraticEvaluationMatrix_det

set_option autoImplicit true
open CompactnessConjecture
variable {K : Type*} [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hroot₀ : symmetricQuadratic a b c x₀ y₀ = 0)
    (hroot₁ : symmetricQuadratic a b c x₁ y₁ = 0)
    (hroot₂ : symmetricQuadratic a b c x₂ y₂ = 0) : False := by
  let A := symmetricQuadraticEvaluationMatrix x₀ y₀ x₁ y₁ x₂ y₂
  have hdet : A.det ≠ 0 := by
    rw [symmetricQuadraticEvaluationMatrix_det]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero htwo h01) h02) h12
  have hmul : A.mulVec ![a, b, c] = 0 := by
    funext i
    fin_cases i
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₀
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₁
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₂
  have hzero : ![a, b, c] = (0 : Fin 3 → K) :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  have ha : a = 0 := congrFun hzero 0
  have hb : b = 0 := congrFun hzero 1
  have hc : c = 0 := congrFun hzero 2
  exact hcoeff.elim (fun h => h ha)
    (fun h => h.elim (fun h' => h' hb) (fun h' => h' hc))
end CompactnessConjecture
