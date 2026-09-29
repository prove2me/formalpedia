-- Prove2me | solution 1 for Erdos180.gluedThetaBase_color_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:57:03.964426+00:00
-- url     : https://prove2.me/submissions/b0e63578-afcc-41bb-b2a3-041f543dfcbd

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Theorems.Thm_Erdos180_thetaCopy_base_center_color_eq

namespace Erdos180

noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma thetaCopy_base_color_eq
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (copy : SimpleGraph.Copy thetaGraph G)
    (first second : Fin 3) :
    color (copy (.inl (.inl first))) =
      color (copy (.inl (.inl second))) := by
  calc
    color (copy (.inl (.inl first))) =
        color (copy (.inl (.inr (0 : Fin 2)))) :=
      thetaCopy_base_center_color_eq color copy first 0
    _ = color (copy (.inl (.inl second))) :=
      (thetaCopy_base_center_color_eq color copy second 0).symm

end

end Erdos180

open Erdos180
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem solution
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (color : G.Coloring (Fin 2))
    (copy : Fin 2) (base : Fin 3) :
    color (copies copy (.inl (.inl base))) =
      color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  fin_cases copy
  · exact thetaCopy_base_color_eq color (copies 0) base 0
  · calc
      color (copies 1 (.inl (.inl base))) =
          color (copies 1 (.inl (.inl (1 : Fin 3)))) :=
        thetaCopy_base_color_eq color (copies 1) base 1
      _ = color (copies 0 (.inl (.inl (1 : Fin 3)))) :=
        congrArg color hfirst
      _ = color (copies 0 (.inl (.inl (0 : Fin 3)))) :=
        thetaCopy_base_color_eq color (copies 0) 1 0
