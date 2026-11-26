-- Prove2me | solution 1 for BKAR.Forest.rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder_orderedCubeSectorContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:36:26.467286+00:00
-- url     : https://prove2.me/submissions/1c125c64-5fce-4d5b-bd60-122f81661546

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_order_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_orderedContribution_eq_orderedCubeSectorContribution_of_contDiff
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    rootBoundarySupportOrderContribution choices ρ I order.val =
      (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
        order.val ρ := by
  rw [rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder
    choices I order ρ]
  exact
    (grownForestForSupportOrder choices I order)
      |>.orderedContribution_eq_orderedCubeSectorContribution_of_contDiff
        (grownForestForSupportOrder_order_mem_edgeOrders choices I order)
        ρ hρ
end BKAR.Forest
