-- Prove2me | solution 2 for BurauFaithful.spec_reduced_coxeter
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-10-01T00:26:54.041101+00:00
-- url     : https://prove2.me/submissions/b477eb7e-0966-4cd0-af58-15db0df031d1

import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

/-- Coxeter relations for the two integral matrices of the `t = -1` specialization of the reduced Burau
representation: the braid relation, `(AB)^4 = 1`, both determinants, and `(AB)^6 = 1`. -/
theorem solution :
    ((!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![2, -1; 1, 0] * !![1, -1; 0, 1] =
        !![2, -1; 1, 0] * !![1, -1; 0, 1] * !![2, -1; 1, 0]) ∧
      ((!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![2, -1; 1, 0] * !![1, -1; 0, 1]) ^ 4 =
        1 ∧
      (!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 ∧
      (!![2, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 ∧
      ((!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![2, -1; 1, 0]) ^ 6 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, pow_succ, Matrix.one_fin_two]
  · simp [Matrix.det_fin_two]
  · simp [Matrix.det_fin_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, pow_succ, Matrix.one_fin_two]
