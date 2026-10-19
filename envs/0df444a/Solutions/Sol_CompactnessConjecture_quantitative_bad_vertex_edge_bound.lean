-- Prove2me | solution 1 for CompactnessConjecture.quantitative_bad_vertex_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/e9f17698-b814-47df-a0ca-43c6c672d959

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_edge_mul_pred_sq_le_bad_card_mul

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex) :
    host.edgeFinset.card * (d - 1) ^ 2 ≤
      (gammaBadVertices host).card * n :=
  proposedFamilyFree_edge_mul_pred_sq_le_bad_card_mul
    host hfree hbip d hdegree
end CompactnessConjecture
