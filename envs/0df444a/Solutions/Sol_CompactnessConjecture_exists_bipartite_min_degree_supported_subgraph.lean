-- Prove2me | solution 1 for CompactnessConjecture.exists_bipartite_min_degree_supported_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/fc54f52d-ada8-4d75-a4f5-9e02d6491850

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_edgeFinset_card_eq_natCard
import Theorems.Thm_CompactnessConjecture_degree_eq_natCard_neighborSet
import Theorems.Thm_CompactnessConjecture_exists_bipartite_half_edges
import Theorems.Thm_CompactnessConjecture_exists_maximum_sharp_pruning_subgraph
import Theorems.Thm_CompactnessConjecture_maximum_sharp_pruning_subgraph_degree
import Theorems.Thm_CompactnessConjecture_maximum_sharp_pruning_subgraph_edge_positive

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hpositive : 0 < G.edgeFinset.card) :
    ∃ H : SimpleGraph V,
      H.IsBipartite ∧ H ≤ G ∧ 0 < Nat.card H.edgeSet ∧
      ∀ v : V, v ∈ H.support →
        G.edgeFinset.card ≤ 2 * Fintype.card V * H.degree v := by
  classical
  obtain ⟨cut, hcutBipartite, hcutSubgraph, hcutEdges⟩ :=
    exists_bipartite_half_edges G
  obtain ⟨H, hH, hpotential, hscore⟩ :=
    exists_maximum_sharp_pruning_subgraph cut (Nat.card G.edgeSet)
  refine ⟨H, SimpleGraph.Colorable.mono_left hH hcutBipartite,
    le_trans hH hcutSubgraph,
    maximum_sharp_pruning_subgraph_edge_positive
      G cut H hpositive hcutEdges hscore, ?_⟩
  intro v hv
  simpa only [edgeFinset_card_eq_natCard,
    degree_eq_natCard_neighborSet] using
    (maximum_sharp_pruning_subgraph_degree
      cut H (Nat.card G.edgeSet) hH hpotential hv)
end CompactnessConjecture
