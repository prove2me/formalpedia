-- Prove2me | solution 1 for Erdos180.mem_gammaBadVertices
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:57:45.501424+00:00
-- url     : https://prove2.me/submissions/0dfbcddb-edb4-47b1-8a53-ad8a8b456c19

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos180
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem solution (G : SimpleGraph V) (v : V) :
    v ∈ gammaBadVertices G ↔ ¬ GammaGood G v := by
  classical
  simp [gammaBadVertices]
