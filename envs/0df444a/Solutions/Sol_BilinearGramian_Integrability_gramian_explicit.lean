-- Prove2me | solution 1 for BilinearGramian.Integrability.gramian_explicit
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-18T09:12:06.306108+00:00
-- url     : https://prove2.me/submissions/1eb62c0d-1303-48ec-913a-291ed7e787b5

import Mathlib
import Definitions.Def_BilinearGramian_Integrability_LinGramian
import Definitions.Def_BilinearGramian_Integrability_Example33

open Matrix BilinearGramian.Integrability

theorem solution (ν ξ : ℝ) (hνξ : 1 + ν * ξ ≠ 0) (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : IsLinGramian exA (fun _ : Fin 1 => exN ν) exB (ξ • ![1, 1]) P) :
    P = (1 + ν * ξ) ^ 2 • !![1 / 2, 1 / 3; 1 / 3, 1 / 4] ∧
      P⁻¹ = (6 / (1 + ν * ξ) ^ 2) • !![3, -4; -4, 6] := by
  have entries (i j : Fin 2) := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) hP
  simp only [IsLinGramian] at hP
  have h00 := entries 0 0
  have h01 := entries 0 1
  have h10 := entries 1 0
  have h11 := entries 1 1
  norm_num [exA, exN, exB, exb, gramRHS, Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.transpose_apply] at h00 h01 h10 h11
  have heq : P = (1 + ν * ξ) ^ 2 • !![1 / 2, 1 / 3; 1 / 3, 1 / 4] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num <;> nlinarith
  refine ⟨heq, ?_⟩
  apply Matrix.inv_eq_right_inv
  rw [heq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

#print axioms solution
