-- Prove2me | solution 1 for BKAR.Forest.edgeParamFinEquivOfOrder_apply_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:55:12.285011+00:00
-- url     : https://prove2.me/submissions/97186094-523f-442b-b96d-372527232f38

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (i : Fin order.length) :
    (F.edgeParamFinEquivOfOrder horder i).val = order.get i := by
  rfl
end BKAR.Forest
