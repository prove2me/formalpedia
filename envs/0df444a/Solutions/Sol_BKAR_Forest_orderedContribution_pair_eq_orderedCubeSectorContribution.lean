-- Prove2me | solution 1 for BKAR.Forest.orderedContribution_pair_eq_orderedCubeSectorContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:03.393227+00:00
-- url     : https://prove2.me/submissions/4cb9676b-0e91-40ef-b3da-8fb717cd83e0

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
import Theorems.Thm_BKAR_Forest_orderedPairSector_setIntegral_eq_iterated_interval
import Theorems.Thm_BKAR_Forest_orderedCubeSectorContribution_pair_eq_orderedPairSectorIntegral
import Theorems.Thm_BKAR_Forest_orderedContribution_pair_eq_nested_pairMeasurableEquivIntegral
import Theorems.Thm_BKAR_Forest_integrableOn_orderedPairSector_pairIntegrand
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
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    F.orderedContribution [e₁, e₂] ρ =
      F.orderedCubeSectorContribution [e₁, e₂] ρ := by
  let pairIntegrand : ℝ × ℝ → ℝ :=
    fun z =>
      mixedPartialList [e₁, e₂].reverse ρ
        (F.standardInterp
          ((F.pairMeasurableEquivOfPair
            (F.edges_eq_pair_of_pair_mem_edgeOrders horder)
            (F.ne_of_pair_mem_edgeOrders horder)).symm z))
  have hint : IntegrableOn pairIntegrand orderedPairSector :=
    F.integrableOn_orderedPairSector_pairIntegrand horder ρ hρ
  calc
    F.orderedContribution [e₁, e₂] ρ
        = ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁, pairIntegrand (t₁, t₂) := by
          exact F.orderedContribution_pair_eq_nested_pairMeasurableEquivIntegral
            horder ρ
    _ = ∫ z in orderedPairSector, pairIntegrand z := by
          exact (orderedPairSector_setIntegral_eq_iterated_interval pairIntegrand hint).symm
    _ = F.orderedCubeSectorContribution [e₁, e₂] ρ := by
          exact (F.orderedCubeSectorContribution_pair_eq_orderedPairSectorIntegral
            horder ρ).symm
end BKAR.Forest
