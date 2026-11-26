-- Prove2me | solution 1 for BKAR.Forest.orderedCubeSectorContribution_pair_eq_orderedPairSectorIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:09.194496+00:00
-- url     : https://prove2.me/submissions/01ab2a72-a810-48fa-8731-29da92829108

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
import Theorems.Thm_BKAR_Forest_setIntegral_orderedCubeSimplex_pair_eq_orderedPairSector
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedCubeSectorContribution [e₁, e₂] ρ =
      ∫ z in orderedPairSector,
        mixedPartialList [e₁, e₂].reverse ρ
          (F.standardInterp
            ((F.pairMeasurableEquivOfPair
              (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
              (F.ne_of_pair_mem_edgeOrders horder)).symm z)) := by
  rw [orderedCubeSectorContribution]
  exact F.setIntegral_orderedCubeSimplex_pair_eq_orderedPairSector horder
    (fun u => mixedPartialList [e₁, e₂].reverse ρ (F.standardInterp u))
end BKAR.Forest
