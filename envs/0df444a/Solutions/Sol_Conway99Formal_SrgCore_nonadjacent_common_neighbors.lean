-- Prove2me | solution 1 for Conway99Formal.SrgCore.nonadjacent_common_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T04:10:05.738983+00:00
-- url     : https://prove2.me/submissions/b71b2b39-9cf1-4331-ab6c-dd789f930477

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
    Fintype.card (G.commonNeighbors u v) = 2 :=
  h.of_not_adj hne huv
