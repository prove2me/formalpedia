-- Prove2me | solution 1 for BKAR.Forest.orderedContribution_eq_orderedCubeSectorContribution_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:48:27.627409+00:00
-- url     : https://prove2.me/submissions/a1f59190-2fba-4869-a9b1-4ed1702403b5

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_orderedContribution_eq_orderedSimplexIntegral_orderMeasurableEquiv_symm
import Theorems.Thm_BKAR_Forest_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
import Theorems.Thm_BKAR_Forest_orderedSimplexIntegral_eq_setIntegral_orderedFinSimplex_of_continuous
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_continuous
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_continuous_orderMeasurableEquivOfOrder_symm
import Theorems.Thm_BKAR_Forest_standardInterp_continuous_comp
import Theorems.Thm_BKAR_ListPathContinuous_comp


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
    F.orderedContribution order ρ =
      F.orderedCubeSectorContribution order ρ := by
  let G : (Fin order.length → ℝ) → ℝ :=
    fun ts =>
      mixedPartialList order.reverse ρ
        (F.standardInterp
          ((F.orderMeasurableEquivOfOrder horder).symm ts))
  have hG : Continuous G := by
    have hcoords :
        Continuous
          (fun ts : Fin order.length → ℝ =>
            (F.orderMeasurableEquivOfOrder horder).symm ts) :=
      F.continuous_orderMeasurableEquivOfOrder_symm horder
    exact (hρ.mixedPartialList_continuous order.reverse).comp
      (F.standardInterp_continuous_comp hcoords)
  calc
    F.orderedContribution order ρ =
      orderedSimplexIntegral order
        (fun ts => G (fun i : Fin order.length => ts.getD i.val 0)) := by
        exact F.orderedContribution_eq_orderedSimplexIntegral_orderMeasurableEquiv_symm
          horder ρ
    _ = ∫ xs in orderedFinSimplex order.length, G xs := by
        exact orderedSimplexIntegral_eq_setIntegral_orderedFinSimplex_of_continuous
          order G hG
    _ = F.orderedCubeSectorContribution order ρ := by
        exact (F.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral horder ρ).symm
end BKAR.Forest
