-- Prove2me | solution 1 for Erdos9796Mission.smaller_counterexample_of_removable
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-12T21:05:45.332027+00:00
-- url     : https://prove2.me/submissions/7ebc1c30-66c9-40b5-ac95-b5f01adb6e3e

import Definitions.Def_Erdos9796Mission_RemovableVertex

open Erdos9796Mission
open Finset

namespace RemovableVertexGlue

lemma convexIndep_erase {A : Finset Plane} (hconv : ConvexIndep (A : Set Plane))
    (x : Plane) : ConvexIndep (A.erase x : Set Plane) := by
  intro a ha hm
  exact hconv a (erase_subset x A ha)
    (convexHull_mono (Set.sdiff_subset_sdiff_left
      (coe_subset.mpr (erase_subset x A))) hm)

end RemovableVertexGlue

theorem solution
    {A : Finset Plane} (hconv : ConvexIndep (A : Set Plane))
    {x : Plane} (hrem : IsRemovableVertex A x) (hcard : 1 < A.card) :
    ∃ B : Finset Plane, B.Nonempty ∧ B.card < A.card ∧
      ConvexIndep (B : Set Plane) ∧ HasNEquidistantProperty 4 B := by
  refine ⟨A.erase x, ?_, ?_, RemovableVertexGlue.convexIndep_erase hconv x, hrem.2⟩
  · rw [← Finset.card_pos, Finset.card_erase_of_mem hrem.1]
    omega
  · exact Finset.card_erase_lt_of_mem hrem.1
