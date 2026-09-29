-- Prove2me | solution 1 for Erdos180.symplecticQuadrangle_encodeFiniteGraph_free_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:14:40.4566+00:00
-- url     : https://prove2.me/submissions/0e050a03-2b90-4833-beaa-ee7806e1d5e4

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Field.Defs
import Mathlib.Combinatorics.SimpleGraph.Copy

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    (encodeFiniteGraph G).graph.Free
        (symplecticQuadrangle K) ↔
      G.Free (symplecticQuadrangle K) :=
  (SimpleGraph.free_congr_left
    (SimpleGraph.Iso.map (Fintype.equivFin V) G)).symm
