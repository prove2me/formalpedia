-- Prove2me | solution 1 for D1Bound5.scalar_last_block_det
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:19.883968+00:00
-- url     : https://prove2.me/submissions/2ef03810-5fb7-4d8d-ad9a-128a7a56f9b9

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Matrix

namespace D1Bound5

/-- Scalar Schur determinant identity without invertibility of the leading block. -/
theorem _root_.solution
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (b c : n → ℂ) (d : ℂ) (hd : d ≠ 0) :
    (Matrix.fromBlocks A (fun i (_ : Fin 1) => b i)
      (fun (_ : Fin 1) j => c j)
      (fun (_ _ : Fin 1) => d)).det =
      d * (A - Matrix.of (fun i j => b i * c j / d)).det := by
  let B : Matrix n (Fin 1) ℂ := fun i _ => b i
  let C : Matrix (Fin 1) n ℂ := fun _ j => c j
  let D : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => d
  have hi : D * Matrix.of (fun (_ _ : Fin 1) => d⁻¹) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    change (∑ k : Fin 1, D 0 k * d⁻¹) = 1
    simp only [Fin.sum_univ_one]
    change d * d⁻¹ = 1
    exact mul_inv_cancel₀ hd
  have hj : Matrix.of (fun (_ _ : Fin 1) => d⁻¹) * D = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    change (∑ k : Fin 1, d⁻¹ * D k 0) = 1
    simp only [Fin.sum_univ_one]
    change d⁻¹ * d = 1
    exact inv_mul_cancel₀ hd
  letI : Invertible D := ⟨Matrix.of (fun (_ _ : Fin 1) => d⁻¹), hj, hi⟩
  have hc : A - B * ⅟D * C =
      A - Matrix.of (fun i j => b i * c j / d) := by
    ext i j
    change A i j - (∑ k : Fin 1, (∑ l : Fin 1, b i * d⁻¹) * c j) =
      A i j - b i * c j / d
    simp only [Fin.sum_univ_one]
    simp [div_eq_mul_inv]
    ring
  change (Matrix.fromBlocks A B C D).det =
    d * (A - Matrix.of (fun i j => b i * c j / d)).det
  rw [Matrix.det_fromBlocks₂₂ A B C D]
  simp only [Matrix.det_fin_one, show D 0 0 = d from rfl, hc]





end D1Bound5
end
