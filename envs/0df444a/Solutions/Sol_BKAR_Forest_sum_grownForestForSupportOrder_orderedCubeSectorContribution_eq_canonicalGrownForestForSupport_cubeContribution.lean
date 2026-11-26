-- Prove2me | solution 1 for BKAR.Forest.sum_grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonicalGrownForestForSupport_cubeContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:34.938979+00:00
-- url     : https://prove2.me/submissions/c2cb4b47-ae77-4321-88c7-04dadf1e3aa5

import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Definitions.Def_BKAR_OrderedAssembly_CubeFold
import Theorems.Thm_BKAR_Forest_sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_canonicalGrownForestForSupport
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonical


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    Finset.sum (edgeSetOrders I.edges).attach
      (fun order =>
        (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
          order.val ρ) =
      (canonicalGrownForestForSupport choices I).cubeContribution ρ := by
  calc
    Finset.sum (edgeSetOrders I.edges).attach
        (fun order =>
          (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
            order.val ρ)
        =
      Finset.sum (edgeSetOrders I.edges).attach
        (fun order =>
          (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
            order.val ρ) := by
        apply Finset.sum_congr rfl
        intro order _horder
        exact
          grownForestForSupportOrder_orderedCubeSectorContribution_eq_canonical
            choices I order ρ
    _ =
      Finset.sum (edgeSetOrders I.edges)
        (fun order =>
          (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
            order ρ) := by
        exact
          Finset.sum_attach (edgeSetOrders I.edges)
            (fun order =>
              (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
                order ρ)
    _ = (canonicalGrownForestForSupport choices I).cubeContribution ρ :=
        sum_edgeSetOrders_orderedCubeSectorContribution_eq_cubeContribution_canonicalGrownForestForSupport
          choices I ρ hρ
end BKAR.Forest
