-- Prove2me | solution 1 for Conway99Formal.FiniteFields.finite_field_identities_20261003
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-03T23:51:08.854736+00:00
-- url     : https://prove2.me/submissions/81aa5be7-93a8-4f6d-b736-2e3118f0056c

import Definitions.Def_Conway99_Finite_Fields_20261003

set_option autoImplicit false

namespace Conway99Formal.FiniteFields

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem complement_adjacency (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Type*) [Ring R] [DecidableEq R] :
    Gᶜ.adjMatrix R = J R - 1 - G.adjMatrix R := by
  have h := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := R)
  rw [G.compl_adjMatrix_eq_adjMatrix_compl R] at h
  change Gᶜ.adjMatrix R = (of 1 : Matrix V V R) - 1 - G.adjMatrix R
  linear_combination (norm := module) h

/-- The strongly regular adjacency equation in the graph's literal vertex coordinates. -/
theorem adjacency_square {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (R : Type*) [Ring R] [DecidableEq R] :
    (G.adjMatrix R) ^ 2 = 12 • (1 : Matrix V V R) - G.adjMatrix R + 2 • J R := by
  have hm := h.matrix_eq (α := R)
  rw [complement_adjacency G R] at hm
  rw [hm]
  module

private theorem adjacency_mul_J {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (R : Type*) [Ring R] (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R * J R = d • J R := by
  ext i j
  have key := G.adjMatrix_mulVec_const_apply_of_regular (α := R) (a := 1) hd (v := i)
  simp only [Matrix.mulVec, dotProduct, Function.const, mul_one] at key
  simp only [Matrix.mul_apply, J, Matrix.of_apply, Pi.one_apply, mul_one,
    Matrix.smul_apply]
  simpa using key

private theorem J_mul_J (R : Type*) [Ring R] :
    (J R : Matrix V V R) * J R = (Fintype.card V) • J R := by
  ext i j
  simp [J, Matrix.mul_apply]

/-- Modulo two, the adjacency operator of a hypothetical Conway graph is a projector. -/
theorem adjacency_idempotent_mod2 {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2) = G.adjMatrix (ZMod 2) := by
  have hneg : ∀ x : ZMod 2, -x = x := by decide
  have h12 : (12 : ℕ) • (1 : Matrix V V (ZMod 2)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), show ((12 : ℕ) : ZMod 2) = 0 by decide, zero_smul]
  have h2 : (2 : ℕ) • (J (V := V) (ZMod 2)) = (0 : Matrix V V (ZMod 2)) := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_smul]
  have hs := adjacency_square h (ZMod 2)
  rw [sq, h12, h2, zero_sub, add_zero] at hs
  calc
    G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2)
        = -G.adjMatrix (ZMod 2) := hs
    _ = G.adjMatrix (ZMod 2) := by ext i j; exact hneg _

/-- The two complementary binary projectors have ranks summing to the vertex count. -/
theorem binary_complementary_ranks {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix (ZMod 2)).rank +
      ((1 : Matrix V V (ZMod 2)) + G.adjMatrix (ZMod 2)).rank = 99 := by
  let A : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)
  have hp : IsIdempotentElem A.mulVecLin := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul]
    exact congrArg Matrix.mulVecLin (by simpa [A] using adjacency_idempotent_mod2 h)
  have hneg : -A.mulVecLin = A.mulVecLin := by
    apply LinearMap.ext
    intro x
    funext i
    change -(A.mulVecLin x i) = A.mulVecLin x i
    have hz : ∀ z : ZMod 2, -z = z := by decide
    exact hz _
  have hB : ((1 : Matrix V V (ZMod 2)) + A).mulVecLin = 1 - A.mulVecLin := by
    rw [Matrix.mulVecLin_add, Matrix.mulVecLin_one, sub_eq_add_neg, hneg]
    rfl
  calc
    (G.adjMatrix (ZMod 2)).rank +
        ((1 : Matrix V V (ZMod 2)) + G.adjMatrix (ZMod 2)).rank =
      Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) +
        Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) := by
          change Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) +
            Module.finrank (ZMod 2)
              (LinearMap.range (((1 : Matrix V V (ZMod 2)) + A).mulVecLin)) = _
          rw [hB, ← LinearMap.IsIdempotentElem.ker_eq_range_one_sub hp]
    _ = Fintype.card V := by
      simpa using LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    _ = 99 := h.card

/-- C04's rank-45 consequence, with its still-open rank-54 premise kept explicit. -/
theorem binary_one_add_rank_of_rank54 {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2)
    (h54 : (G.adjMatrix (ZMod 2)).rank = 54) :
    ((1 : Matrix V V (ZMod 2)) + G.adjMatrix (ZMod 2)).rank = 45 := by
  have hr := binary_complementary_ranks h
  omega

/-- Modulo seven, the graph-owned Seidel matrix has square zero. -/
theorem seidel_square_mod7 {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    seidel G (ZMod 7) * seidel G (ZMod 7) = 0 := by
  let A : Matrix V V (ZMod 7) := G.adjMatrix (ZMod 7)
  let U : Matrix V V (ZMod 7) := J (ZMod 7)
  have hAA : A * A = 12 • (1 : Matrix V V (ZMod 7)) - A + 2 • U := by
    simpa [A, U, sq] using adjacency_square h (ZMod 7)
  have hAU : A * U = 14 • U := by
    simpa [A, U] using (adjacency_mul_J (ZMod 7) h.regular)
  have hUA : U * A = 14 • U := by
    have hJ : (J (ZMod 7) : Matrix V V (ZMod 7))ᵀ = J (ZMod 7) := by
      ext i j
      rfl
    have ht := congrArg Matrix.transpose hAU
    rw [Matrix.transpose_mul, show Uᵀ = U by simpa [U] using hJ,
      show Aᵀ = A by simpa [A] using
        (SimpleGraph.transpose_adjMatrix (G := G) (α := ZMod 7)),
      Matrix.transpose_smul, show Uᵀ = U by simpa [U] using hJ] at ht
    exact ht
  have hUU : U * U = 99 • U := by
    simpa [U, h.card] using (J_mul_J (V := V) (ZMod 7))
  have hraw : (U - 1 - 2 • A) * (U - 1 - 2 • A)
      = 49 • (1 : Matrix V V (ZMod 7)) + 49 • U := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, smul_smul, hAA, hAU, hUA, hUU,
      smul_add, smul_sub]
    abel
  have h49 : ∀ M : Matrix V V (ZMod 7), (49 : ℕ) • M = 0 := fun M => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 7), show ((49 : ℕ) : ZMod 7) = 0 by decide,
      zero_smul]
  simpa [seidel, A, U, h49] using hraw

/-- The form `x² + y²` is anisotropic over `𝔽₇`. -/
theorem square_sum_zero_mod7 (x y : ZMod 7) (h : x ^ 2 + y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  revert x y
  decide

/-- The companion one-variable form has no nonzero zero over `𝔽₇`. -/
theorem four_square_zero_mod7 (x : ZMod 7) (h : 4 * x ^ 2 = 0) : x = 0 := by
  revert x
  decide

/-- Prospective private theorem: three necessary finite-field identities for one graph. -/
theorem solution {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2) = G.adjMatrix (ZMod 2)) ∧
    ((G.adjMatrix (ZMod 2)).rank +
      ((1 : Matrix V V (ZMod 2)) + G.adjMatrix (ZMod 2)).rank = 99) ∧
    (seidel G (ZMod 7) * seidel G (ZMod 7) = 0) ∧
    (∀ x y : ZMod 7, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0) ∧
    (∀ x : ZMod 7, 4 * x ^ 2 = 0 → x = 0) := by
  exact ⟨adjacency_idempotent_mod2 h, binary_complementary_ranks h,
    seidel_square_mod7 h,
    fun x y hxy => square_sum_zero_mod7 x y hxy,
    fun x hx => four_square_zero_mod7 x hx⟩

/-- Stable qualified statement for the private finite-field checkpoint. -/
theorem finite_field_identities_20261003 {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2) = G.adjMatrix (ZMod 2)) ∧
    ((G.adjMatrix (ZMod 2)).rank +
      ((1 : Matrix V V (ZMod 2)) + G.adjMatrix (ZMod 2)).rank = 99) ∧
    (seidel G (ZMod 7) * seidel G (ZMod 7) = 0) ∧
    (∀ x y : ZMod 7, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0) ∧
    (∀ x : ZMod 7, 4 * x ^ 2 = 0 → x = 0) :=
  solution h

#print axioms adjacency_square
#print axioms adjacency_idempotent_mod2
#print axioms binary_complementary_ranks
#print axioms binary_one_add_rank_of_rank54
#print axioms seidel_square_mod7
#print axioms square_sum_zero_mod7
#print axioms four_square_zero_mod7
#print axioms solution
#print axioms finite_field_identities_20261003

end Conway99Formal.FiniteFields

/-- Private server entry point with the catalog theorem's exact type. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) :
    (G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2) = G.adjMatrix (ZMod 2)) ∧
    ((G.adjMatrix (ZMod 2)).rank +
      ((1 : Matrix V V (ZMod 2)) + G.adjMatrix (ZMod 2)).rank = 99) ∧
    (Conway99Formal.FiniteFields.seidel G (ZMod 7) *
      Conway99Formal.FiniteFields.seidel G (ZMod 7) = 0) ∧
    (∀ x y : ZMod 7, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0) ∧
    (∀ x : ZMod 7, 4 * x ^ 2 = 0 → x = 0) := by
  exact Conway99Formal.FiniteFields.finite_field_identities_20261003 h

#print axioms solution
