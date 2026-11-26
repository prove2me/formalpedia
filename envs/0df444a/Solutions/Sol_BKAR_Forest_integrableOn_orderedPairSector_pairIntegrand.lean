-- Prove2me | solution 1 for BKAR.Forest.integrableOn_orderedPairSector_pairIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:14.457854+00:00
-- url     : https://prove2.me/submissions/fc12ec5e-74c0-466d-8efa-a29883a2cfb1

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
import Theorems.Thm_BKAR_Forest_measurableSet_orderedPairSector
import Theorems.Thm_BKAR_Forest_measurePreserving_pairMeasurableEquivOfPair
import Theorems.Thm_BKAR_Forest_orderedCubeSimplex_pair_eq_pairMeasurableEquiv_preimage_orderedPairSector
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_integrableOn_orderedCubeSectorIntegrand
import Theorems.Thm_BKAR_Forest_orderedCubeSimplex_subset_unitCube


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    IntegrableOn
      (fun z : ℝ × ℝ =>
        mixedPartialList [e₁, e₂].reverse ρ
          (F.standardInterp
            ((F.pairMeasurableEquivOfPair
              (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
              (F.ne_of_pair_mem_edgeOrders horder)).symm z)))
      orderedPairSector := by
  let hedges := F.edges_eq_pair_of_pair_mem_edgeOrders horder
  let hne := F.ne_of_pair_mem_edgeOrders horder
  let φ : (F.EdgeParam → ℝ) ≃ᵐ (ℝ × ℝ) :=
    F.pairMeasurableEquivOfPair hedges hne
  let H : (F.EdgeParam → ℝ) → ℝ :=
    fun u => mixedPartialList [e₁, e₂].reverse ρ (F.standardInterp u)
  have hsector :
      F.orderedCubeSimplex [e₁, e₂] = φ ⁻¹' orderedPairSector := by
    exact F.orderedCubeSimplex_pair_eq_pairMeasurableEquiv_preimage_orderedPairSector
      horder
  have hH_unit : IntegrableOn H F.unitCube :=
    F.integrableOn_orderedCubeSectorIntegrand [e₁, e₂] ρ hρ
  have hH_pre : IntegrableOn H (φ ⁻¹' orderedPairSector) := by
    rw [← hsector]
    exact hH_unit.mono_set (F.orderedCubeSimplex_subset_unitCube [e₁, e₂])
  have hcomp :
      IntegrableOn ((fun z : ℝ × ℝ => H (φ.symm z)) ∘ φ)
        (φ ⁻¹' orderedPairSector) := by
    refine hH_pre.congr_fun ?_ (measurableSet_orderedPairSector.preimage φ.measurable)
    intro u _hu
    exact congrArg H (φ.left_inv u).symm
  exact
    ((F.measurePreserving_pairMeasurableEquivOfPair hedges hne).integrableOn_comp_preimage
      (MeasurableEquiv.measurableEmbedding φ)
      (f := fun z : ℝ × ℝ => H (φ.symm z))
      (s := orderedPairSector)).mp hcomp
end BKAR.Forest
