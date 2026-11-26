-- Prove2me | solution 1 for BKAR.Forest.setIntegral_orderedCubeSimplex_pair_eq_orderedPairSector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:44.946535+00:00
-- url     : https://prove2.me/submissions/060e1921-b2e3-49c9-ab18-197674113118

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
import Theorems.Thm_BKAR_Forest_measurableSet_orderedPairSector
import Theorems.Thm_BKAR_Forest_measurePreserving_pairMeasurableEquivOfPair
import Theorems.Thm_BKAR_Forest_orderedCubeSimplex_pair_eq_pairMeasurableEquiv_preimage_orderedPairSector

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (g : (F.EdgeParam → ℝ) → ℝ) :
    ∫ u in F.orderedCubeSimplex [e₁, e₂], g u
        ∂(volume : Measure (F.EdgeParam → ℝ)) =
      ∫ z in orderedPairSector,
        g ((F.pairMeasurableEquivOfPair
          (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
          (F.ne_of_pair_mem_edgeOrders horder)).symm z) := by
  let hedges := F.edges_eq_pair_of_pair_mem_edgeOrders horder
  let hne := F.ne_of_pair_mem_edgeOrders horder
  let φ : (F.EdgeParam → ℝ) ≃ᵐ (ℝ × ℝ) :=
    F.pairMeasurableEquivOfPair hedges hne
  have hsector :
      F.orderedCubeSimplex [e₁, e₂] = φ ⁻¹' orderedPairSector := by
    exact F.orderedCubeSimplex_pair_eq_pairMeasurableEquiv_preimage_orderedPairSector
      horder
  rw [hsector]
  have hpre :=
    (F.measurePreserving_pairMeasurableEquivOfPair hedges hne).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding φ)
      (fun z : ℝ × ℝ => g (φ.symm z)) orderedPairSector
  have hcongr :
      ∫ u in φ ⁻¹' orderedPairSector, g u
          ∂(volume : Measure (F.EdgeParam → ℝ)) =
        ∫ u in φ ⁻¹' orderedPairSector, g (φ.symm (φ u))
          ∂(volume : Measure (F.EdgeParam → ℝ)) := by
    apply setIntegral_congr_fun
    · exact measurableSet_orderedPairSector.preimage φ.measurable
    · intro u _hu
      exact congrArg g (φ.left_inv u).symm
  exact hcongr.trans hpre
end BKAR.Forest
