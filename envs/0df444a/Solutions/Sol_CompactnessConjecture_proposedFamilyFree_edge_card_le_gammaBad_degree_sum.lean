-- Prove2me | solution 1 for CompactnessConjecture.proposedFamilyFree_edge_card_le_gammaBad_degree_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/48068d23-6cf5-4405-a7fa-50c07478f0ab

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_edge_has_gammaBad
import Theorems.Thm_CompactnessConjecture_edgeFinset_card_le_sum_degree_of_vertex_cover

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite) :
    host.edgeFinset.card ≤
      ∑ v ∈ gammaBadVertices host, host.degree v :=
  edgeFinset_card_le_sum_degree_of_vertex_cover
    host (gammaBadVertices host)
    (fun _ _ hedge => proposedFamilyFree_edge_has_gammaBad
      host hfree hbip hedge)
end CompactnessConjecture
