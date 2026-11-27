-- Prove2me | solution 1 for C6BipartiteDomination.corona_core_leaves_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:12.505325+00:00
-- url     : https://prove2.me/submissions/e630e968-ff9d-4b45-8310-07f5a33cc7c5

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset CoronaVertex) :
    Disjoint (coronaSelectedCoreVertices D) (coronaForcedLeaves D) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvC hvL
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvC
  obtain ⟨p, hp, hEq⟩ := Finset.mem_image.mp hvL
  cases hEq
end C6BipartiteDomination
