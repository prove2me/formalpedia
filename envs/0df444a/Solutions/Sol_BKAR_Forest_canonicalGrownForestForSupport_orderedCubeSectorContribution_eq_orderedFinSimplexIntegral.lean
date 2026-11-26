-- Prove2me | solution 1 for BKAR.Forest.canonicalGrownForestForSupport_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:04:01.8626+00:00
-- url     : https://prove2.me/submissions/2f0f0a6e-41bf-4b0f-95b1-f12505902268

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_order_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
        order.val ρ =
      ∫ ts in orderedFinSimplex order.val.length,
        mixedPartialList order.val.reverse ρ
          ((canonicalGrownForestForSupport choices I).standardInterp
            ((Forest.orderMeasurableEquivOfOrder
                (canonicalGrownForestForSupport choices I)
                (canonicalGrownForestForSupport_order_mem_edgeOrders
                  choices I order.property)).symm ts)) :=
  (canonicalGrownForestForSupport choices I)
    |>.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
      (canonicalGrownForestForSupport_order_mem_edgeOrders
        choices I order.property) ρ
end BKAR.Forest
