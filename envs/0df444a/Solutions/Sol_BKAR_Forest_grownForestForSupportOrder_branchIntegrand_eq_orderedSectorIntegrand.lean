-- Prove2me | solution 1 for BKAR.Forest.grownForestForSupportOrder_branchIntegrand_eq_orderedSectorIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:36:11.526258+00:00
-- url     : https://prove2.me/submissions/570a3c83-ec52-4542-b269-431e29af65a5

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_def_standardInterp
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
    (ρ : (Edge V → ℝ) → ℝ)
    (ts : List ℝ) (hlen : ts.length = order.val.length) :
    (grownForestForSupportOrder_orderedGrowth choices I order).branchIntegrand
        emptyParam ρ ts =
      mixedPartialList order.val.reverse ρ
        ((grownForestForSupportOrder choices I order).standardInterp
          ((grownForestForSupportOrder choices I order).paramsOfOrder
            order.val ts)) := by
  rw [OrderedGrowth.branchIntegrand_def_standardInterp]
  rw [OrderedGrowth.params_emptyStart_eq_paramsOfOrder_of_length
    (grownForestForSupportOrder_orderedGrowth choices I order) hlen]
end BKAR.Forest
