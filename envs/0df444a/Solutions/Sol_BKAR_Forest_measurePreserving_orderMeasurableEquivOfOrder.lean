-- Prove2me | solution 1 for BKAR.Forest.measurePreserving_orderMeasurableEquivOfOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:57:08.263538+00:00
-- url     : https://prove2.me/submissions/ae8ea785-a4e0-4067-b1b9-4f38826f3b56

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
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    MeasurePreserving (F.orderMeasurableEquivOfOrder horder)
      (volume : Measure (F.EdgeParam → ℝ))
      (volume : Measure (Fin order.length → ℝ)) := by
  let φ : (Fin order.length → ℝ) ≃ᵐ (F.EdgeParam → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinEquivOfOrder horder)
  have hφ : MeasurePreserving φ
      (volume : Measure (Fin order.length → ℝ))
      (volume : Measure (F.EdgeParam → ℝ)) :=
    volume_measurePreserving_piCongrLeft (fun _ : F.EdgeParam => ℝ)
      (F.edgeParamFinEquivOfOrder horder)
  exact MeasurePreserving.symm φ hφ
end BKAR.Forest
