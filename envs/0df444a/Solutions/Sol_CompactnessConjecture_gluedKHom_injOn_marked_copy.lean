-- Prove2me | solution 1 for CompactnessConjecture.gluedKHom_injOn_marked_copy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/280e9ee1-918f-4e74-8b28-315b372212b2

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
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    (index : Fin 2) :
    Set.InjOn (gluedKHom copies hjoining)
      {vertex : KVertex | vertex.1 = index} := by
  rintro ⟨leftIndex, leftVertex⟩ hleft
    ⟨rightIndex, rightVertex⟩ hright heq
  change leftIndex = index at hleft
  change rightIndex = index at hright
  subst leftIndex
  subst rightIndex
  change copies index leftVertex = copies index rightVertex at heq
  have hvertices := (copies index).injective heq
  subst rightVertex
  rfl
end CompactnessConjecture
