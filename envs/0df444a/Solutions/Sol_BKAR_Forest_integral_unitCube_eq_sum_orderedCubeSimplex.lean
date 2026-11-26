-- Prove2me | solution 1 for BKAR.Forest.integral_unitCube_eq_sum_orderedCubeSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:39:34.322881+00:00
-- url     : https://prove2.me/submissions/b538fb16-cbea-4110-86a6-cc084f5cf7a7

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Theorems.Thm_BKAR_Forest_integral_unitCube_eq_tsum_orderedCubeSimplex

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (f : (F.EdgeParam → ℝ) → ℝ)
    (hfi : IntegrableOn f F.unitCube
      (volume : Measure (F.EdgeParam → ℝ))) :
    ∫ u in F.unitCube, f u ∂(volume : Measure (F.EdgeParam → ℝ)) =
      Finset.sum
        (Finset.univ :
          Finset {order : List (Edge V) // order ∈ F.edgeOrders})
        (fun order =>
          ∫ u in F.orderedCubeSimplex order.val, f u
            ∂(volume : Measure (F.EdgeParam → ℝ))) := by
  rw [F.integral_unitCube_eq_tsum_orderedCubeSimplex f hfi]
  rw [tsum_fintype]
end BKAR.Forest
