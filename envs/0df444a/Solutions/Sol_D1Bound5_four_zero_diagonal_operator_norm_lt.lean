-- Prove2me | solution 1 for D1Bound5.four_zero_diagonal_operator_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:11:48.194001+00:00
-- url     : https://prove2.me/submissions/954bc511-8fe9-4cd9-9ead-9f9e08167c67

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_MatrixOperatorNorm_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5





private theorem swap01_23_val (i : Fin 4) :
    swap01_23 i = if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 3 else 2 := by
  fin_cases i <;> decide
private theorem swap02_13_val (i : Fin 4) :
    swap02_13 i = if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0 else 1 := by
  fin_cases i <;> decide
private theorem swap03_12_val (i : Fin 4) :
    swap03_12 i = if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 1 else 0 := by
  fin_cases i <;> decide

private theorem perm_matrix_at (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    (σ.permMatrix ℂ) i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

private theorem matching_matrix_at (E : Matrix (Fin 4) (Fin 4) ℂ)
    (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    (Matrix.diagonal (fun i => E i (σ i)) * σ.permMatrix ℂ) i j =
      if σ i = j then E i j else 0 := by
  rw [Matrix.diagonal_mul, perm_matrix_at]
  by_cases h : σ i = j
  · simpa only [if_pos h, mul_one] using congrArg (E i) h
  · simp [h]

private theorem three_matchings (E : Matrix (Fin 4) (Fin 4) ℂ)
    (hd : ∀ i, E i i = 0) :
    E = (Matrix.diagonal (fun i => E i (swap01_23 i)) *
      swap01_23.permMatrix ℂ) +
      (Matrix.diagonal (fun i => E i (swap02_13 i)) *
      swap02_13.permMatrix ℂ) +
      (Matrix.diagonal (fun i => E i (swap03_12 i)) *
      swap03_12.permMatrix ℂ) := by
  ext i j
  simp only [Matrix.add_apply, matching_matrix_at]
  fin_cases i <;> fin_cases j <;>
    simp [swap01_23_val, swap02_13_val, swap03_12_val, hd]

end D1Bound5

namespace D1Bound5

private theorem matching_norm_lt (E : Matrix (Fin 4) (Fin 4) ℂ)
    (σ : Equiv.Perm (Fin 4)) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : ∀ i, ‖E i (σ i)‖ < δ) :
    ‖Matrix.diagonal (fun i => E i (σ i)) * σ.permMatrix ℂ‖ < δ := by
  have hd : ‖(Matrix.diagonal (fun i => E i (σ i)))‖ < δ := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_lt_iff hδ).2 hsmall
  calc
    ‖Matrix.diagonal (fun i => E i (σ i)) * σ.permMatrix ℂ‖
        ≤ ‖Matrix.diagonal (fun i => E i (σ i))‖ * ‖σ.permMatrix ℂ‖ :=
          Matrix.l2_opNorm_mul _ _
    _ ≤ ‖Matrix.diagonal (fun i => E i (σ i))‖ := by
      exact mul_le_of_le_one_right (norm_nonneg _) (Matrix.permMatrix_l2_opNorm_le σ)
    _ < δ := hd

private theorem swap01_ne_self (i : Fin 4) : i ≠ swap01_23 i := by
  fin_cases i <;> decide
private theorem swap02_ne_self (i : Fin 4) : i ≠ swap02_13 i := by
  fin_cases i <;> decide
private theorem swap03_ne_self (i : Fin 4) : i ≠ swap03_12 i := by
  fin_cases i <;> decide

/-- An entrywise bound on a zero-diagonal 4x4 complex matrix yields an
L2-operator norm bound with factor three. No symmetry is required.
The proof partitions the off-diagonal positions into three perfect
matchings, each represented by a diagonal times a permutation matrix. -/
theorem _root_.solution
    (E : Matrix (Fin 4) (Fin 4) ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ i, E i i = 0)
    (hoff : ∀ i j, i ≠ j → ‖E i j‖ < δ) :
    ‖E‖ < 3 * δ := by
  let P : Matrix (Fin 4) (Fin 4) ℂ :=
    Matrix.diagonal (fun i => E i (swap01_23 i)) * swap01_23.permMatrix ℂ
  let Q : Matrix (Fin 4) (Fin 4) ℂ :=
    Matrix.diagonal (fun i => E i (swap02_13 i)) * swap02_13.permMatrix ℂ
  let R : Matrix (Fin 4) (Fin 4) ℂ :=
    Matrix.diagonal (fun i => E i (swap03_12 i)) * swap03_12.permMatrix ℂ
  have hPQ : E = P + Q + R := three_matchings E hd
  have hP : ‖P‖ < δ := matching_norm_lt E swap01_23 δ hδ
    (fun i => hoff i (swap01_23 i) (swap01_ne_self i))
  have hQ : ‖Q‖ < δ := matching_norm_lt E swap02_13 δ hδ
    (fun i => hoff i (swap02_13 i) (swap02_ne_self i))
  have hR : ‖R‖ < δ := matching_norm_lt E swap03_12 δ hδ
    (fun i => hoff i (swap03_12 i) (swap03_ne_self i))
  calc
    ‖E‖ = ‖P + Q + R‖ := congrArg norm hPQ
    _ ≤ ‖P‖ + ‖Q‖ + ‖R‖ := by
      have h₁ := norm_add_le P Q
      have h₂ := norm_add_le (P + Q) R
      linarith
    _ < 3 * δ := by linarith

end D1Bound5
end
