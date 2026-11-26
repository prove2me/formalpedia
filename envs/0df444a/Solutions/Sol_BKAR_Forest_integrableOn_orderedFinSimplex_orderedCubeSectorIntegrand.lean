-- Prove2me | solution 1 for BKAR.Forest.integrableOn_orderedFinSimplex_orderedCubeSectorIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:08.833034+00:00
-- url     : https://prove2.me/submissions/2f62bd56-81f0-4d4e-8f9c-1537c6eb3bfd

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_integrableOn_orderedCubeSectorIntegrand
import Theorems.Thm_BKAR_Forest_measurableSet_orderedCubeSimplex
import Theorems.Thm_BKAR_Forest_measurePreserving_orderMeasurableEquivOfOrder
import Theorems.Thm_BKAR_Forest_orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex
import Theorems.Thm_BKAR_Forest_orderedCubeSimplex_subset_unitCube


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
    IntegrableOn
      (fun ts : Fin order.length → ℝ =>
        mixedPartialList order.reverse ρ
          (F.standardInterp
            ((F.orderMeasurableEquivOfOrder horder).symm ts)))
      (orderedFinSimplex order.length) := by
  let φ : (F.EdgeParam → ℝ) ≃ᵐ (Fin order.length → ℝ) :=
    F.orderMeasurableEquivOfOrder horder
  let H : (F.EdgeParam → ℝ) → ℝ :=
    fun u => mixedPartialList order.reverse ρ (F.standardInterp u)
  have hsector :
      F.orderedCubeSimplex order = φ ⁻¹' orderedFinSimplex order.length := by
    exact F.orderedCubeSimplex_eq_orderMeasurableEquiv_preimage_orderedFinSimplex
      horder
  have hH_unit : IntegrableOn H F.unitCube :=
    F.integrableOn_orderedCubeSectorIntegrand order ρ hρ
  have hH_pre : IntegrableOn H (φ ⁻¹' orderedFinSimplex order.length) := by
    rw [← hsector]
    exact hH_unit.mono_set (F.orderedCubeSimplex_subset_unitCube order)
  have hmeas : MeasurableSet (φ ⁻¹' orderedFinSimplex order.length) := by
    rw [← hsector]
    exact F.measurableSet_orderedCubeSimplex order
  have hcomp :
      IntegrableOn ((fun ts : Fin order.length → ℝ => H (φ.symm ts)) ∘ φ)
        (φ ⁻¹' orderedFinSimplex order.length) := by
    refine hH_pre.congr_fun ?_ hmeas
    intro u _hu
    exact congrArg H (φ.left_inv u).symm
  exact
    ((F.measurePreserving_orderMeasurableEquivOfOrder horder).integrableOn_comp_preimage
      (MeasurableEquiv.measurableEmbedding φ)
      (f := fun ts : Fin order.length → ℝ => H (φ.symm ts))
      (s := orderedFinSimplex order.length)).mp hcomp
end BKAR.Forest
