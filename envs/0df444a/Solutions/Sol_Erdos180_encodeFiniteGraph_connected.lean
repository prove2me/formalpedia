-- Prove2me | solution 1 for Erdos180.encodeFiniteGraph_connected
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:26:54.033961+00:00
-- url     : https://prove2.me/submissions/710b2bf3-053f-48fd-88b2-8f1ade59c314

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Erdos180
open Finset SimpleGraph

theorem solution
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hconnected : graph.Connected) :
    (encodeFiniteGraph graph).graph.Connected := by
  change (graph.map (Fintype.equivFin V).toEmbedding).Connected
  exact (SimpleGraph.Iso.connected_iff
    (SimpleGraph.Iso.map (Fintype.equivFin V) graph)).mp hconnected
