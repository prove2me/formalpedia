-- Prove2me | solution 1 for Conway99Formal.PointFrame.point_gram_identities_20261003
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-03T23:51:10.324698+00:00
-- url     : https://prove2.me/submissions/75946063-742e-4fbf-af8e-7c515b75b346

import Definitions.Def_Conway99_Point_Gram_20261003

set_option autoImplicit false

/-! A complete proof of six graph-owned point Gram identities. -/

namespace Conway99Formal.PointFrame

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem complement_matrix (G : SimpleGraph V) [DecidableRel G.Adj] :
    Gᶜ.adjMatrix ℝ = (of 1 : Matrix V V ℝ) - 1 - G.adjMatrix ℝ := by
  have h := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := ℝ)
  rw [G.compl_adjMatrix_eq_adjMatrix_compl ℝ] at h
  linear_combination (norm := module) h

private theorem adjacency_square {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    G.adjMatrix ℝ * G.adjMatrix ℝ =
      12 • (1 : Matrix V V ℝ) - G.adjMatrix ℝ + 2 • of 1 := by
  have hm := h.matrix_eq (α := ℝ)
  rw [complement_matrix G] at hm
  have hs : G.adjMatrix ℝ * G.adjMatrix ℝ = (G.adjMatrix ℝ) ^ 2 := by rw [sq]
  rw [hs, hm]
  module

private theorem adjacency_mul_ones {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    G.adjMatrix ℝ * (of 1 : Matrix V V ℝ) = 14 • of 1 := by
  ext i j
  have key := G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) h.regular (v := i)
  simp only [Matrix.mulVec, dotProduct, Function.const, mul_one] at key
  simp only [Matrix.mul_apply, Matrix.of_apply, Pi.one_apply, mul_one, Matrix.smul_apply]
  simpa using key

private theorem ones_mul_adjacency {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (of 1 : Matrix V V ℝ) * G.adjMatrix ℝ = 14 • of 1 := by
  have hJ : ((of 1 : Matrix V V ℝ))ᵀ = of 1 := by ext i j; rfl
  have ht := congrArg Matrix.transpose (adjacency_mul_ones h)
  rw [Matrix.transpose_mul, hJ, SimpleGraph.transpose_adjMatrix,
    Matrix.transpose_smul, hJ] at ht
  exact ht

private theorem ones_square (hcard : Fintype.card V = 99) :
    (of 1 : Matrix V V ℝ) * (of 1 : Matrix V V ℝ) = 99 • of 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.of_apply, hcard]

/-- The point Gram matrix is 63 times a real idempotent. -/
theorem Q_square {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : Q G * Q G = 63 • Q G := by
  simp only [Q, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, smul_smul,
    adjacency_square h, adjacency_mul_ones h, ones_mul_adjacency h,
    ones_square h.card, smul_add, smul_sub]
  abel

/-- The graph-owned Gram is symmetric. -/
theorem Q_transpose (G : SimpleGraph V) [DecidableRel G.Adj] : (Q G)ᵀ = Q G := by
  have hJ : ((of 1 : Matrix V V ℝ))ᵀ = of 1 := by ext i j; rfl
  simp only [Q, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, SimpleGraph.transpose_adjMatrix, hJ]

/-- The Gram is zero on the all-ones direction. -/
theorem Q_mul_ones {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    Q G * (of 1 : Matrix V V ℝ) = 0 := by
  simp only [Q, add_mul, sub_mul, smul_mul_assoc, one_mul,
    adjacency_mul_ones h, ones_square h.card, smul_smul]
  module

theorem trace_Q {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : (Q G).trace = 2772 := by
  simp only [Q, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul]
  have ha : (G.adjMatrix ℝ).trace = 0 := by simp [Matrix.trace, Matrix.diag]
  have hj : (of 1 : Matrix V V ℝ).trace = 99 := by
    simp [Matrix.trace, Matrix.diag, h.card]
  have hi : (1 : Matrix V V ℝ).trace = 99 := by
    rw [Matrix.trace_one, h.card]
    norm_num
  rw [ha, hj, hi]
  norm_num

theorem P_idempotent {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : P G * P G = P G := by
  simp only [P, Matrix.smul_mul, Matrix.mul_smul, Q_square h,
    ← Nat.cast_smul_eq_nsmul, smul_smul]
  module

theorem trace_P {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) : (P G).trace = 44 := by
  rw [P, Matrix.trace_smul, trace_Q h, smul_eq_mul]
  norm_num

/-- Necessary Gram and projector equations of a hypothetical Conway graph. -/
theorem point_gram_identities_20261003 {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (Q G * Q G = 63 • Q G) ∧
    ((Q G)ᵀ = Q G) ∧
    (Q G * (of 1 : Matrix V V ℝ) = 0) ∧
    (P G * P G = P G) ∧
    ((Q G).trace = 2772) ∧
    ((P G).trace = 44) := by
  exact ⟨Q_square h, Q_transpose G, Q_mul_ones h, P_idempotent h,
    trace_Q h, trace_P h⟩

#print axioms Conway99Formal.PointFrame.Q_square
#print axioms Conway99Formal.PointFrame.Q_transpose
#print axioms Conway99Formal.PointFrame.Q_mul_ones
#print axioms Conway99Formal.PointFrame.trace_Q
#print axioms Conway99Formal.PointFrame.P_idempotent
#print axioms Conway99Formal.PointFrame.trace_P
#print axioms Conway99Formal.PointFrame.point_gram_identities_20261003

end Conway99Formal.PointFrame

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (Conway99Formal.PointFrame.Q G * Conway99Formal.PointFrame.Q G =
      63 • Conway99Formal.PointFrame.Q G) ∧
    (Matrix.transpose (Conway99Formal.PointFrame.Q G) =
      Conway99Formal.PointFrame.Q G) ∧
    (Conway99Formal.PointFrame.Q G * (Matrix.of 1 : Matrix V V ℝ) = 0) ∧
    (Conway99Formal.PointFrame.P G * Conway99Formal.PointFrame.P G =
      Conway99Formal.PointFrame.P G) ∧
    ((Conway99Formal.PointFrame.Q G).trace = 2772) ∧
    ((Conway99Formal.PointFrame.P G).trace = 44) :=
  Conway99Formal.PointFrame.point_gram_identities_20261003 h

#print axioms solution
