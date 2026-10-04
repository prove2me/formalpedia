-- Prove2me | solution 1 for Conway99Formal.SrgCore.quadratic_form_expansion
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T02:49:18.030728+00:00
-- url     : https://prove2.me/submissions/d17d29bd-1896-43b1-8ee6-b1dea977c556

import Mathlib

namespace Conway99Formal.SrgCore
end Conway99Formal.SrgCore

set_option autoImplicit false

/-! Graph-owned parameter and adjacency identities for a hypothetical SRG(99,14,1,2).
Sources: `Conway99/Conway99/Core.lean` §§1–3, 8.1;
`Conway99/Conway99/Claims/C01srgcorealgebra.lean` §§0, 3, 6;
`Conway99/results/R005_star_complement_square_discriminant.md`.
-/

namespace Conway99Formal.SrgCore

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



































theorem complement_adjacency (α : Type*) [Ring α] [DecidableEq α] :
    Gᶜ.adjMatrix α = (of 1 : Matrix V V α) - 1 - G.adjMatrix α := by
  have heq := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := α)
  rw [G.compl_adjMatrix_eq_adjMatrix_compl α] at heq
  linear_combination (norm := module) heq

theorem adjacency_square (h : G.IsSRGWith 99 14 1 2)
    (α : Type*) [Ring α] [DecidableEq α] :
    (G.adjMatrix α) ^ 2 =
      12 • (1 : Matrix V V α) - G.adjMatrix α + 2 • (of 1 : Matrix V V α) := by
  have hm := h.matrix_eq (α := α)
  rw [complement_adjacency G α] at hm
  rw [hm]
  module


















end Conway99Formal.SrgCore

set_option autoImplicit false

/-! Graph-owned parameter and adjacency identities for a hypothetical SRG(99,14,1,2).
Sources: `Conway99/Conway99/Core.lean` §§1–3, 8.1;
`Conway99/Conway99/Claims/C01srgcorealgebra.lean` §§0, 3, 6;
`Conway99/results/R005_star_complement_square_discriminant.md`.
-/

open Conway99Formal.SrgCore

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Conway99Formal.SrgCore in
theorem solution (h : G.IsSRGWith 99 14 1 2)
    (S : Finset V) :
    (∑ i ∈ S, ∑ j ∈ S, (G.adjMatrix ℤ * G.adjMatrix ℤ) i j) =
      12 * (S.card : ℤ) -
        (∑ i ∈ S, ∑ j ∈ S, G.adjMatrix ℤ i j) + 2 * (S.card : ℤ) ^ 2 := by
  have hentry (i j : V) :
      (G.adjMatrix ℤ * G.adjMatrix ℤ) i j =
        (if i = j then 12 else 0) - G.adjMatrix ℤ i j + 2 := by
    have heq := congrArg (fun M : Matrix V V ℤ => M i j) (adjacency_square G h ℤ)
    simp only [sq, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply] at heq
    simpa [Matrix.one_apply, Matrix.of_apply] using heq
  have hdiag : (∑ i ∈ S, ∑ j ∈ S, (if i = j then (12 : ℤ) else 0)) =
      12 * (S.card : ℤ) := by
    simp
    ring
  have hconst : (∑ i ∈ S, ∑ j ∈ S, (2 : ℤ)) =
      2 * (S.card : ℤ) ^ 2 := by
    simp only [sum_const, nsmul_eq_mul]
    ring
  calc
    (∑ i ∈ S, ∑ j ∈ S, (G.adjMatrix ℤ * G.adjMatrix ℤ) i j) =
        ∑ i ∈ S, ∑ j ∈ S,
          ((if i = j then 12 else 0) - G.adjMatrix ℤ i j + 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hentry i j
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [hdiag, hconst]
