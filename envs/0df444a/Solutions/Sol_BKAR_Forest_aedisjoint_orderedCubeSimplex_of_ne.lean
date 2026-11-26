-- Prove2me | solution 1 for BKAR.Forest.aedisjoint_orderedCubeSimplex_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:59.297572+00:00
-- url     : https://prove2.me/submissions/76914be0-eaec-42d6-9661-e1835ff8b45d

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Theorems.Thm_BKAR_Forest_measure_collisionSet_eq_zero
import Theorems.Thm_BKAR_Forest_orderedCubeSimplex_inter_subset_collisionSet_of_ne

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
    AEDisjoint (volume : Measure (F.EdgeParam → ℝ))
      (F.orderedCubeSimplex order₁) (F.orderedCubeSimplex order₂) := by
  exact measure_mono_null
    (F.orderedCubeSimplex_inter_subset_collisionSet_of_ne horder₁ horder₂ hne)
    F.measure_collisionSet_eq_zero
end BKAR.Forest
