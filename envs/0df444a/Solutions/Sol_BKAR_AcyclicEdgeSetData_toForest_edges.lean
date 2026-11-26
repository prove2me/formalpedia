-- Prove2me | solution 1 for BKAR.AcyclicEdgeSetData.toForest_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:05:10.244839+00:00
-- url     : https://prove2.me/submissions/d8b4e10b-47de-4abd-b320-78cd7c21b69d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_ForestGraph

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.AcyclicEdgeSetData
open EdgePath
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.AcyclicEdgeSetData
theorem _root_.solution {S : Finset (Edge V)} (data : AcyclicEdgeSetData S) :
    data.toForest.edges = S :=
  rfl
end BKAR.AcyclicEdgeSetData
