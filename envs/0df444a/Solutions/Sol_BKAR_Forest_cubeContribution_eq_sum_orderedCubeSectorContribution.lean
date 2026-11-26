-- Prove2me | solution 1 for BKAR.Forest.cubeContribution_eq_sum_orderedCubeSectorContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:50.377114+00:00
-- url     : https://prove2.me/submissions/47fdf18c-412d-44ae-a2d6-a8c8c5da5beb

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Theorems.Thm_BKAR_Forest_cubeContribution_eq_sum_orderedCubeSimplex_mixedPartial
import Theorems.Thm_BKAR_Forest_orderedCubeSectorContribution_eq_integral_mixedPartial

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
      Finset.sum F.edgeOrders
        (fun order => F.orderedCubeSectorContribution order ρ) := by
  rw [F.cubeContribution_eq_sum_orderedCubeSimplex_mixedPartial ρ hρ]
  calc
    (∑ order : {order : List (Edge V) // order ∈ F.edgeOrders},
        ∫ u in F.orderedCubeSimplex order.val,
          F.mixedPartial ρ (F.standardInterp u)
            ∂(volume : Measure (F.EdgeParam → ℝ))) =
        Finset.sum F.edgeOrders
          (fun order =>
            ∫ u in F.orderedCubeSimplex order,
              F.mixedPartial ρ (F.standardInterp u)
                ∂(volume : Measure (F.EdgeParam → ℝ))) := by
          rw [← Finset.attach_eq_univ (s := F.edgeOrders)]
          exact
            (Finset.sum_attach F.edgeOrders
              (fun order =>
                ∫ u in F.orderedCubeSimplex order,
                  F.mixedPartial ρ (F.standardInterp u)
                    ∂(volume : Measure (F.EdgeParam → ℝ))))
    _ = Finset.sum F.edgeOrders
          (fun order => F.orderedCubeSectorContribution order ρ) := by
          apply Finset.sum_congr rfl
          intro order horder
          exact (F.orderedCubeSectorContribution_eq_integral_mixedPartial
            horder ρ hρ).symm
end BKAR.Forest
