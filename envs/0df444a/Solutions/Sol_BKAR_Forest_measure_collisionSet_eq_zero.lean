-- Prove2me | solution 1 for BKAR.Forest.measure_collisionSet_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:32.138923+00:00
-- url     : https://prove2.me/submissions/93a5b79a-c56a-45d8-96c6-c1e58df17d72

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Theorems.Thm_BKAR_Forest_measure_coordinateCollision_eq_zero

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) :
    (volume : Measure (F.EdgeParam → ℝ)) F.collisionSet = 0 := by
  classical
  rw [collisionSet]
  exact measure_iUnion_null fun p =>
    F.measure_coordinateCollision_eq_zero p.val.1 p.val.2 p.property
end BKAR.Forest
