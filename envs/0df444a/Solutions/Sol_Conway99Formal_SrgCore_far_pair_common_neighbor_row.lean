-- Prove2me | solution 1 for Conway99Formal.SrgCore.far_pair_common_neighbor_row
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T02:49:17.205592+00:00
-- url     : https://prove2.me/submissions/be75bc42-01f6-4194-9051-51f8b32d84dc

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









theorem offdiagonal_two_walk (h : G.IsSRGWith 99 14 1 2)
    (u v : V) (huv : u ≠ v) :
    (∑ w, G.adjMatrix ℤ u w * G.adjMatrix ℤ w v) + G.adjMatrix ℤ u v = 2 := by
  have heq := congrArg (fun M : Matrix V V ℤ => M u v) (adjacency_square G h ℤ)
  simp only [sq, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply] at heq
  simp [Matrix.of_apply, huv, SimpleGraph.adjMatrix_apply] at heq ⊢
  omega








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
    (u v : V) (huv : u ≠ v) :
    (∑ w, G.adjMatrix ℤ u w * G.adjMatrix ℤ v w) + G.adjMatrix ℤ u v = 2 := by
  have hsymm (w : V) : G.adjMatrix ℤ v w = G.adjMatrix ℤ w v := by
    simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
  calc
    (∑ w, G.adjMatrix ℤ u w * G.adjMatrix ℤ v w) + G.adjMatrix ℤ u v =
        (∑ w, G.adjMatrix ℤ u w * G.adjMatrix ℤ w v) + G.adjMatrix ℤ u v := by
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      rw [hsymm]
    _ = 2 := offdiagonal_two_walk G h u v huv
