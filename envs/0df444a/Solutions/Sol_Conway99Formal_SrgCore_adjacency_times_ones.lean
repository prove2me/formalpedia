-- Prove2me | solution 1 for Conway99Formal.SrgCore.adjacency_times_ones
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T03:32:45.274055+00:00
-- url     : https://prove2.me/submissions/176ea1b5-6d78-4f44-ad3c-22a1913a8969

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
    (α : Type*) [Ring α] :
    G.adjMatrix α * (of 1 : Matrix V V α) = 14 • (of 1 : Matrix V V α) := by
  ext i j
  have key := G.adjMatrix_mulVec_const_apply_of_regular (α := α) (a := 1)
    h.regular (v := i)
  simp only [Matrix.mulVec, dotProduct, Function.const, mul_one] at key
  simp only [Matrix.mul_apply, Matrix.of_apply, Pi.one_apply, mul_one,
    Matrix.smul_apply]
  simpa using key
