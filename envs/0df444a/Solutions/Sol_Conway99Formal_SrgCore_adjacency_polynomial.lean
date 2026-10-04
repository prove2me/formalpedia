-- Prove2me | solution 1 for Conway99Formal.SrgCore.adjacency_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T04:14:35.645992+00:00
-- url     : https://prove2.me/submissions/d06a1387-3923-4678-a4f5-1cf9451d0b74

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
    (α : Type*) [CommRing α] [DecidableEq α] :
    (G.adjMatrix α - 3 • (1 : Matrix V V α)) *
      (G.adjMatrix α + 4 • (1 : Matrix V V α)) =
        2 • (of 1 : Matrix V V α) := by
  have hA := adjacency_square G h α
  have h2 : (G.adjMatrix α - 3 • (1 : Matrix V V α)) *
      (G.adjMatrix α + 4 • (1 : Matrix V V α)) =
        (G.adjMatrix α) ^ 2 + G.adjMatrix α - 12 • (1 : Matrix V V α) := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, sq]
    noncomm_ring
  rw [h2, hA]
  module
