-- Prove2me | solution 1 for Erdos180.thetaCopy_base_center_color_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:56:22.500283+00:00
-- url     : https://prove2.me/submissions/9bf51c71-3cb4-4c1a-875f-c79908da6652

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

open Erdos180
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem solution
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (copy : SimpleGraph.Copy thetaGraph G)
    (base : Fin 3) (center : Fin 2) :
    color (copy (.inl (.inl base))) =
      color (copy (.inl (.inr center))) := by
  exact bipartite_coloring_eq_of_common_neighbor color
    (copy.toHom.map_rel (theta_base_pair_adj base center))
    (copy.toHom.map_rel (theta_center_pair_adj base center))
