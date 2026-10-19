-- Prove2me | solution 1 for CompactnessConjecture.familyFree_of_embedded_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/56e461bf-2eca-48a7-973c-f9d482f68701

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Classical Topology
namespace CompactnessConjecture
theorem _root_.solution
    {family : Finset FiniteGraph}
    {n N : ℕ} (host : SimpleGraph (Fin n))
    (subgraph : SimpleGraph (Fin N))
    (embedding : Fin N ↪ Fin n)
    (hsub : subgraph.map embedding ≤ host)
    (hfree : FamilyFree family host) :
    FamilyFree family subgraph := by
  intro forbidden hforbidden hcontained
  exact hfree forbidden hforbidden
    ((hcontained.trans
      ⟨(SimpleGraph.Embedding.map embedding subgraph).toCopy⟩).mono_right hsub)
end CompactnessConjecture
