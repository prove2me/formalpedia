-- Prove2me | solution 1 for Conway99Formal.SrgCore.offdiagonal_two_walk
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T04:14:41.270977+00:00
-- url     : https://prove2.me/submissions/4d073e27-a9ce-48b0-803c-7c971a7dde10

import Theorems.Thm_Conway99Formal_SrgCore_complement_adjacency
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
    (u v : V) (huv : u ≠ v) :
    (∑ w, G.adjMatrix ℤ u w * G.adjMatrix ℤ w v) + G.adjMatrix ℤ u v = 2 := by
  have heq := congrArg (fun M : Matrix V V ℤ => M u v) (adjacency_square G h ℤ)
  simp only [sq, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply] at heq
  simp [Matrix.of_apply, huv, SimpleGraph.adjMatrix_apply] at heq ⊢
  omega
