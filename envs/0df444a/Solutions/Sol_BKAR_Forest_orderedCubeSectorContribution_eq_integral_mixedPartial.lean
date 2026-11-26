-- Prove2me | solution 1 for BKAR.Forest.orderedCubeSectorContribution_eq_integral_mixedPartial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:02.95503+00:00
-- url     : https://prove2.me/submissions/bc30ce58-f6c4-4ba1-9630-eeefc6e7f911

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Theorems.Thm_BKAR_Forest_mixedPartial_eq_mixedPartialList_of_mem_edgeOrders


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    F.orderedCubeSectorContribution order ρ =
      ∫ u in F.orderedCubeSimplex order,
        F.mixedPartial ρ (F.standardInterp u)
          ∂(volume : Measure (F.EdgeParam → ℝ)) := by
  rw [orderedCubeSectorContribution]
  rw [F.mixedPartial_eq_mixedPartialList_of_mem_edgeOrders horder hρ]
end BKAR.Forest
