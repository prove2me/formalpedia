-- Prove2me | solution 1 for CompactnessConjecture.gluedJVertex_jThetaVertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/b48426a2-277e-49b5-bb38-1de0748287c0

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
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (copy : Fin 2) (vertex : SubdivisionVertex 2) :
    gluedJVertex copies joining (jThetaVertex copy vertex) =
      copies copy vertex := by
  rcases vertex with (base | center) | pair
  · exact gluedJBase_jBase copies hfirst hsecond copy base
  · simp [jThetaVertex, gluedJVertex]
  · simp [jThetaVertex, gluedJVertex]
end CompactnessConjecture
