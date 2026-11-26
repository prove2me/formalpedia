-- Prove2me | solution 1 for BKAR.Forest.grownForestForSupportOrder_branchPoint_eq_standardInterp_paramsOfOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:35:49.250513+00:00
-- url     : https://prove2.me/submissions/fa753262-bc44-4d53-b8ae-b5d0d9ebd9a0

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_def
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_emptyStart_eq_paramsOfOrder_of_length


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ts : List ℝ) (hlen : ts.length = order.val.length) :
    (grownForestForSupportOrder_orderedGrowth choices I order).branchPoint
        emptyParam ts =
      (grownForestForSupportOrder choices I order).standardInterp
        ((grownForestForSupportOrder choices I order).paramsOfOrder
          order.val ts) := by
  rw [OrderedGrowth.branchPoint_def]
  rw [OrderedGrowth.params_emptyStart_eq_paramsOfOrder_of_length
    (grownForestForSupportOrder_orderedGrowth choices I order) hlen]
end BKAR.Forest
