-- Prove2me | solution 1 for BKAR.Forest.cubeContribution_eq_sum_orderedCubeSimplex_mixedPartial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:57.962606+00:00
-- url     : https://prove2.me/submissions/8e720914-d171-410b-a90a-6fe5b9dbfbac

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Theorems.Thm_BKAR_Forest_integrableOn_cubeContributionIntegrand
import Theorems.Thm_BKAR_Forest_integral_unitCube_eq_sum_orderedCubeSimplex


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    F.cubeContribution ρ =
      Finset.sum
        (Finset.univ :
          Finset {order : List (Edge V) // order ∈ F.edgeOrders})
        (fun order =>
          ∫ u in F.orderedCubeSimplex order.val,
            F.mixedPartial ρ (F.standardInterp u)
              ∂(volume : Measure (F.EdgeParam → ℝ))) := by
  rw [cubeContribution]
  exact F.integral_unitCube_eq_sum_orderedCubeSimplex
    (fun u : F.EdgeParam → ℝ =>
      F.mixedPartial ρ (F.standardInterp u))
    (F.integrableOn_cubeContributionIntegrand ρ hρ)
end BKAR.Forest
