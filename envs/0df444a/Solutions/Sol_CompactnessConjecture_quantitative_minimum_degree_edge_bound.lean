-- Prove2me | solution 1 for CompactnessConjecture.quantitative_minimum_degree_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/3c7dd782-0de6-4ebf-8239-c9ed737be150

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex) :
    n * d ≤ 2 * host.edgeFinset.card := by
  simpa [SimpleGraph.sum_degrees_eq_twice_card_edges] using
    Finset.card_nsmul_le_sum Finset.univ
      (fun vertex : Fin n => host.degree vertex) d
      (fun vertex _ => hdegree vertex)
end CompactnessConjecture
