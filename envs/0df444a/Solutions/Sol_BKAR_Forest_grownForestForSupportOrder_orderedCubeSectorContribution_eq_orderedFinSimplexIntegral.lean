-- Prove2me | solution 1 for BKAR.Forest.grownForestForSupportOrder_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:03:48.641103+00:00
-- url     : https://prove2.me/submissions/97757f97-ff2a-4fd5-84d9-e34f67d5b80e

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_order_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral


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
    (ρ : (Edge V → ℝ) → ℝ) :
    (grownForestForSupportOrder choices I order).orderedCubeSectorContribution
        order.val ρ =
      ∫ ts in orderedFinSimplex order.val.length,
        mixedPartialList order.val.reverse ρ
          ((grownForestForSupportOrder choices I order).standardInterp
            ((Forest.orderMeasurableEquivOfOrder
                (grownForestForSupportOrder choices I order)
                (grownForestForSupportOrder_order_mem_edgeOrders
                  choices I order)).symm ts)) :=
  (grownForestForSupportOrder choices I order)
    |>.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
      (grownForestForSupportOrder_order_mem_edgeOrders choices I order) ρ
end BKAR.Forest
