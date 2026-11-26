-- Prove2me | solution 1 for BKAR.Forest.setIntegral_orderedCubeSimplex_orderMeasurableEquiv_eq_orderedFinSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:58.636847+00:00
-- url     : https://prove2.me/submissions/0ba24884-8b2b-47d9-8d11-811708cd2f21

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Theorems.Thm_BKAR_Forest_measurePreserving_orderMeasurableEquivOfOrder
import Theorems.Thm_BKAR_Forest_orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (g : (Fin order.length → ℝ) → ℝ) :
    ∫ u in F.orderedCubeSimplex order,
        g (F.orderMeasurableEquivOfOrder horder u)
        ∂(volume : Measure (F.EdgeParam → ℝ)) =
      ∫ ts in orderedFinSimplex order.length, g ts := by
  let φ : (F.EdgeParam → ℝ) ≃ᵐ (Fin order.length → ℝ) :=
    F.orderMeasurableEquivOfOrder horder
  have hsector :
      F.orderedCubeSimplex order = φ ⁻¹' orderedFinSimplex order.length := by
    exact F.orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex
      horder
  rw [hsector]
  exact (F.measurePreserving_orderMeasurableEquivOfOrder horder).setIntegral_preimage_emb
    (MeasurableEquiv.measurableEmbedding φ) g (orderedFinSimplex order.length)
end BKAR.Forest
