-- Prove2me | solution 1 for BKAR.Forest.orderedCubeSimplex_inter_subset_collisionSet_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:02.498943+00:00
-- url     : https://prove2.me/submissions/3a666830-5031-4527-b942-5a304233481c

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Theorems.Thm_BKAR_Forest_eq_of_mem_orderedCubeSimplex_of_notMem_collisionSet

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order₁ order₂ : List (Edge V)}
    (horder₁ : order₁ ∈ F.edgeOrders) (horder₂ : order₂ ∈ F.edgeOrders)
    (hne : order₁ ≠ order₂) :
    F.orderedCubeSimplex order₁ ∩ F.orderedCubeSimplex order₂ ⊆
      F.collisionSet := by
  intro u hu
  by_contra hno
  exact hne
    (F.eq_of_mem_orderedCubeSimplex_of_notMem_collisionSet
      horder₁ horder₂ hno hu.1 hu.2)
end BKAR.Forest
