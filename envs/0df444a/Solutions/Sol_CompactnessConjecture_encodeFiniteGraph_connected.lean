-- Prove2me | solution 1 for CompactnessConjecture.encodeFiniteGraph_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/4df93f7b-ab33-44a2-84b3-40f14cea1b87

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hconnected : graph.Connected) :
    (encodeFiniteGraph graph).graph.Connected := by
  change (graph.map (Fintype.equivFin V).toEmbedding).Connected
  exact (SimpleGraph.Iso.connected_iff
    (SimpleGraph.Iso.map (Fintype.equivFin V) graph)).mp hconnected
end CompactnessConjecture
