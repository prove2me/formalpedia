-- Prove2me | solution 1 for Conway99Formal.SrgCore.adjacency_double_sum_internal_degrees
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T03:22:05.286469+00:00
-- url     : https://prove2.me/submissions/149bab3e-32a9-418d-a93c-f20581d6d8b5

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
theorem solution (S : Finset V) :
    (∑ i ∈ S, ∑ j ∈ S, G.adjMatrix ℤ i j) =
      ∑ u ∈ S, ((S ∩ G.neighborFinset u).card : ℤ) := by
  classical
  apply Finset.sum_congr rfl
  intro u hu
  have hset : (S.filter fun v => G.Adj u v) = S ∩ G.neighborFinset u := by
    ext v
    simp only [mem_filter, mem_inter, G.mem_neighborFinset]
  calc
    (∑ v ∈ S, G.adjMatrix ℤ u v) =
        ((S.filter fun v => G.Adj u v).card : ℤ) := by
      simpa only [G.adjMatrix_apply] using
        (Finset.sum_boole (fun v : V => G.Adj u v) S :
          (∑ v ∈ S, if G.Adj u v then (1 : ℤ) else 0) =
            ((S.filter fun v => G.Adj u v).card : ℤ))
    _ = ((S ∩ G.neighborFinset u).card : ℤ) := by rw [hset]
