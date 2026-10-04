-- Prove2me | solution 1 for Conway99Formal.SrgCore.nonadjacent_common_neighbors_finset
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T03:22:40.415966+00:00
-- url     : https://prove2.me/submissions/ebfa5c72-cf21-4ba7-8694-cab9d6056585

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
    (u v : V) (hne : u ≠ v) (huv : ¬ G.Adj u v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card = 2 := by
  calc
    (G.neighborFinset u ∩ G.neighborFinset v).card =
        (G.commonNeighbors u v).toFinset.card := by
      congr 1
      ext w
      have hmem : w ∈ (G.commonNeighbors u v).toFinset ↔
          w ∈ G.commonNeighbors u v := Set.mem_toFinset
      simpa only [Finset.mem_inter, G.mem_neighborFinset,
        G.mem_commonNeighbors] using hmem.symm
    _ = Fintype.card (G.commonNeighbors u v) := Set.toFinset_card _
    _ = 2 := h.of_not_adj hne huv
