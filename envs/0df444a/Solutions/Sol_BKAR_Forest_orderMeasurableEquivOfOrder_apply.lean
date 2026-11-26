-- Prove2me | solution 1 for BKAR.Forest.orderMeasurableEquivOfOrder_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:55:39.161841+00:00
-- url     : https://prove2.me/submissions/95dc57d7-2b5c-431e-b609-eecdbd4f8912

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeOrders
attribute [local simp] BKAR.Forest.paramValue_of_mem



set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (u : F.EdgeParam → ℝ) (i : Fin order.length) :
    F.orderMeasurableEquivOfOrder horder u i =
      F.paramValue u (order.get i) := by
  have he : order.get i ∈ F.edges := by
    have hset := F.toFinset_eq_of_mem_edgeOrders horder
    rw [← hset]
    exact List.mem_toFinset.mpr (List.get_mem order i)
  change
    ((MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinEquivOfOrder horder)).symm u) i =
        F.paramValue u (order.get i)
  change
    ((Equiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinEquivOfOrder horder)).symm u) i =
        F.paramValue u (order.get i)
  rw [F.paramValue_of_mem u he]
  rfl
end BKAR.Forest
