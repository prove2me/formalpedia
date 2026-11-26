-- Prove2me | solution 1 for BKAR.Forest.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:46.788831+00:00
-- url     : https://prove2.me/submissions/a9c4d32d-b5d0-46f4-822e-4e1208f9f2ea

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_setIntegral_orderedCubeSimplex_eq_orderedFinSimplex_symm
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedCubeSectorContribution order ρ =
      ∫ ts in orderedFinSimplex order.length,
        mixedPartialList order.reverse ρ
          (F.standardInterp
            ((F.orderMeasurableEquivOfOrder horder).symm ts)) := by
  rw [orderedCubeSectorContribution]
  exact F.setIntegral_orderedCubeSimplex_eq_orderedFinSimplex_symm horder
    (fun u => mixedPartialList order.reverse ρ (F.standardInterp u))
end BKAR.Forest
