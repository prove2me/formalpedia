-- Prove2me | solution 1 for Conway99Formal.SrgCore.half_internal_degree_sum_eq_induced_edges
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T04:10:02.49849+00:00
-- url     : https://prove2.me/submissions/cf9f5f59-c54e-45eb-a89d-74c53e1ee4dd

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

















private theorem internal_degree_sum_eq_twice_induced_edges (S : Finset V) :
    (∑ u ∈ S, (S ∩ G.neighborFinset u).card) =
      2 * (G.induce (S : Set V)).edgeFinset.card := by
  classical
  letI : Fintype (S : Set V) := FinsetCoe.fintype S
  have hdeg (u : (S : Set V)) :
      (G.induce (S : Set V)).degree u = (S ∩ G.neighborFinset u).card := by
    have hmap :
        ((G.induce (S : Set V)).neighborFinset u).map
            (.subtype (· ∈ (S : Set V))) =
          G.neighborFinset u ∩ (S : Set V).toFinset := by
      ext
      simp
    calc
      (G.induce (S : Set V)).degree u =
          ((G.induce (S : Set V)).neighborFinset u).card := rfl
      _ = (G.neighborFinset u ∩ (S : Set V).toFinset).card := by
        simpa only [Finset.card_map] using
          congrArg Finset.card hmap
      _ = (S ∩ G.neighborFinset u).card := by
        simp only [toFinset_coe, Finset.inter_comm]
  have hs := (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hs
  exact (Finset.sum_coe_sort S
    (fun u => (S ∩ G.neighborFinset u).card)).symm.trans hs






































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
    (∑ u ∈ S, (S ∩ G.neighborFinset u).card) / 2 =
      (G.induce (S : Set V)).edgeFinset.card := by
  have hsum := internal_degree_sum_eq_twice_induced_edges G S
  omega
