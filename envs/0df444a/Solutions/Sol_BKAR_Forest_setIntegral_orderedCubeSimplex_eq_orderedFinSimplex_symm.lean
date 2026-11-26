-- Prove2me | solution 1 for BKAR.Forest.setIntegral_orderedCubeSimplex_eq_orderedFinSimplex_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:11.291293+00:00
-- url     : https://prove2.me/submissions/4f8534b5-5655-4f08-8376-574aadd1b9e3

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_measurableSet_orderedCubeSimplex
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
    (g : (F.EdgeParam → ℝ) → ℝ) :
    ∫ u in F.orderedCubeSimplex order, g u
        ∂(volume : Measure (F.EdgeParam → ℝ)) =
      ∫ ts in orderedFinSimplex order.length,
        g ((F.orderMeasurableEquivOfOrder horder).symm ts) := by
  let φ : (F.EdgeParam → ℝ) ≃ᵐ (Fin order.length → ℝ) :=
    F.orderMeasurableEquivOfOrder horder
  have hsector :
      F.orderedCubeSimplex order = φ ⁻¹' orderedFinSimplex order.length := by
    exact F.orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex
      horder
  rw [hsector]
  have hpre :=
    (F.measurePreserving_orderMeasurableEquivOfOrder horder).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding φ)
      (fun ts : Fin order.length → ℝ => g (φ.symm ts))
      (orderedFinSimplex order.length)
  have hmeas : MeasurableSet (φ ⁻¹' orderedFinSimplex order.length) := by
    rw [← hsector]
    exact F.measurableSet_orderedCubeSimplex order
  have hcongr :
      ∫ u in φ ⁻¹' orderedFinSimplex order.length, g u
          ∂(volume : Measure (F.EdgeParam → ℝ)) =
        ∫ u in φ ⁻¹' orderedFinSimplex order.length, g (φ.symm (φ u))
          ∂(volume : Measure (F.EdgeParam → ℝ)) := by
    apply setIntegral_congr_fun hmeas
    intro u _hu
    exact congrArg g (φ.left_inv u).symm
  exact hcongr.trans hpre
end BKAR.Forest
