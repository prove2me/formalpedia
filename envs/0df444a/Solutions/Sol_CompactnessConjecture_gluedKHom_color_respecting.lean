-- Prove2me | solution 1 for CompactnessConjecture.gluedKHom_color_respecting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/b884e6ce-f419-4299-afc9-e9c87afb0c6a

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_gluedKVertex_color_false_iff

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter)) :
    ∀ left right,
      gluedKHom copies hjoining left =
        gluedKHom copies hjoining right →
      kColor left = kColor right := by
  obtain ⟨color⟩ := hbip
  intro left right heq
  have hhostColor :
      color (gluedKVertex copies left) =
        color (gluedKVertex copies right) :=
    congrArg color heq
  cases hleft : kColor left <;> cases hright : kColor right
  · rfl
  · exfalso
    have hbase :=
      (gluedKVertex_color_false_iff
        copies hjoining color left).mp hleft
    have hfalse :=
      (gluedKVertex_color_false_iff
        copies hjoining color right).mpr
        (hhostColor.symm.trans hbase)
    simp [hright] at hfalse
  · exfalso
    have hbase :=
      (gluedKVertex_color_false_iff
        copies hjoining color right).mp hright
    have hfalse :=
      (gluedKVertex_color_false_iff
        copies hjoining color left).mpr
        (hhostColor.trans hbase)
    simp [hleft] at hfalse
  · rfl
end CompactnessConjecture
