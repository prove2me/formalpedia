-- Prove2me | solution 1 for BKAR.Forest.orderedContribution_eq_orderedSimplexIntegral_orderMeasurableEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:41.093049+00:00
-- url     : https://prove2.me/submissions/f47296a9-bc73-421f-bf17-64aa2f569c3c

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_paramsOfOrder_eq_orderMeasurableEquiv_symm_getD_of_length
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_orderedSimplexIntegral_congr_of_length


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
    F.orderedContribution order ρ =
      orderedSimplexIntegral order
        (fun ts =>
          mixedPartialList order.reverse ρ
            (F.standardInterp
              ((F.orderMeasurableEquivOfOrder horder).symm
                (fun i : Fin order.length => ts.getD i.val 0)))) := by
  rw [orderedContribution]
  apply orderedSimplexIntegral_congr_of_length
  intro ts hlen
  rw [F.paramsOfOrder_eq_orderMeasurableEquiv_symm_getD_of_length horder ts hlen]
end BKAR.Forest
