-- Prove2me | solution 1 for BKAR.Forest.grownForestForSupportOrder_orderedFinSectorIntegrand_eq_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:45.050474+00:00
-- url     : https://prove2.me/submissions/1a2089ed-3047-4585-a32d-9348a380d7ef

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_standardInterp_orderMeasurableEquiv_symm_eq_canonical
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_order_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_order_mem_edgeOrders


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
    (ρ : (Edge V → ℝ) → ℝ)
    (ts : Fin order.val.length → ℝ) :
    mixedPartialList order.val.reverse ρ
        ((grownForestForSupportOrder choices I order).standardInterp
          ((Forest.orderMeasurableEquivOfOrder
              (grownForestForSupportOrder choices I order)
              (grownForestForSupportOrder_order_mem_edgeOrders
                choices I order)).symm ts)) =
      mixedPartialList order.val.reverse ρ
        ((canonicalGrownForestForSupport choices I).standardInterp
          ((Forest.orderMeasurableEquivOfOrder
              (canonicalGrownForestForSupport choices I)
              (canonicalGrownForestForSupport_order_mem_edgeOrders
                choices I order.property)).symm ts)) :=
  congrArg (mixedPartialList order.val.reverse ρ)
    (grownForestForSupportOrder_standardInterp_orderMeasurableEquiv_symm_eq_canonical
      choices I order ts)
end BKAR.Forest
