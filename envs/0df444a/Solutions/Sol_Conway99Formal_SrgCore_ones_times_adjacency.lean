-- Prove2me | solution 1 for Conway99Formal.SrgCore.ones_times_adjacency
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T04:14:01.430696+00:00
-- url     : https://prove2.me/submissions/17601c4d-5d0b-4ba8-be93-507ad609e3b7

import Theorems.Thm_Conway99Formal_SrgCore_adjacency_times_ones
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
    (of 1 : Matrix V V α) * G.adjMatrix α = 14 • (of 1 : Matrix V V α) := by
  have hJ : ((of 1 : Matrix V V α))ᵀ = (of 1 : Matrix V V α) := by ext i j; rfl
  have ht := congrArg Matrix.transpose (adjacency_times_ones G h α)
  rw [Matrix.transpose_mul, hJ, SimpleGraph.transpose_adjMatrix,
    Matrix.transpose_smul, hJ] at ht
  exact ht
