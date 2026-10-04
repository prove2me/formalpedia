-- Prove2me | solution 1 for Conway99Formal.SrgCore.neighborhood_matching
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T04:00:52.881632+00:00
-- url     : https://prove2.me/submissions/f23282aa-109e-47b6-a1f0-47ecbbec5483

import Theorems.Thm_Conway99Formal_SrgCore_neighborhood_internal_degree
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



theorem degree (h : G.IsSRGWith 99 14 1 2) (v : V) : G.degree v = 14 :=
  h.regular.degree_eq v




















































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
theorem solution (h : G.IsSRGWith 99 14 1 2) (u : V) :
    (∀ v : G.neighborSet u, (G.induce (G.neighborSet u)).degree v = 1) ∧
      (G.induce (G.neighborSet u)).edgeFinset.card = 7 := by
  have hlocal (v : G.neighborSet u) :
      (G.induce (G.neighborSet u)).degree v = 1 := by
    have hmap := G.map_neighborFinset_induce (s := G.neighborSet u) v
    have hcard := congrArg Finset.card hmap
    simp only [Finset.card_map, ← G.neighborFinset_def] at hcard
    have hinner := neighborhood_internal_degree G h u v.1 v.2
    change ((G.induce (G.neighborSet u)).neighborFinset v).card = 1
    rw [hcard]
    simpa only [Finset.inter_comm] using hinner
  constructor
  · exact hlocal
  · have hs := (G.induce (G.neighborSet u)).sum_degrees_eq_twice_card_edges
    simp_rw [hlocal] at hs
    simp only [sum_const, card_univ, nsmul_eq_mul] at hs
    rw [G.card_neighborSet_eq_degree, degree G h u] at hs
    omega
