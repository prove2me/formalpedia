-- Prove2me | solution 1 for BKAR.Forest.continuous_orderMeasurableEquivOfOrder_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:37:36.102653+00:00
-- url     : https://prove2.me/submissions/65e6cbc9-74fe-49c9-9dbf-df400496cf63

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Theorems.Thm_BKAR_Forest_orderMeasurableEquivOfOrder_symm_apply

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    Continuous
      (fun ts : Fin order.length → ℝ =>
        (F.orderMeasurableEquivOfOrder horder).symm ts) := by
  apply continuous_pi
  intro p
  have hfun :
      (fun ts : Fin order.length → ℝ =>
          (F.orderMeasurableEquivOfOrder horder).symm ts p) =
        fun ts : Fin order.length → ℝ =>
          ts ((F.edgeParamFinEquivOfOrder horder).symm p) := by
    funext ts
    exact F.orderMeasurableEquivOfOrder_symm_apply horder ts p
  rw [hfun]
  exact continuous_apply ((F.edgeParamFinEquivOfOrder horder).symm p)
end BKAR.Forest
