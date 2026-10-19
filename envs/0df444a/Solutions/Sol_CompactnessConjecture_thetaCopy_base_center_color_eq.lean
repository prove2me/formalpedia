-- Prove2me | solution 1 for CompactnessConjecture.thetaCopy_base_center_color_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/9a1d55f9-0fec-4709-a104-f1e36153c3b7

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (copy : SimpleGraph.Copy thetaGraph G)
    (base : Fin 3) (center : Fin 2) :
    color (copy (.inl (.inl base))) =
      color (copy (.inl (.inr center))) := by
  exact bipartite_coloring_eq_of_common_neighbor color
    (copy.toHom.map_rel (theta_base_pair_adj base center))
    (copy.toHom.map_rel (theta_center_pair_adj base center))
end CompactnessConjecture
