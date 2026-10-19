-- Prove2me | solution 1 for CompactnessConjecture.gluedJBase_color_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/cf09caea-9f6d-42ce-879c-d112ebf4469a

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_gluedThetaBase_color_eq

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
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (color : G.Coloring (Fin 2))
    (base : Fin 4) :
    color (gluedJBase copies base) =
      color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  fin_cases base
  · rfl
  · exact gluedThetaBase_color_eq copies hfirst color 1 0
  · exact gluedThetaBase_color_eq copies hfirst color 0 1
  · exact gluedThetaBase_color_eq copies hfirst color 0 2
end CompactnessConjecture
