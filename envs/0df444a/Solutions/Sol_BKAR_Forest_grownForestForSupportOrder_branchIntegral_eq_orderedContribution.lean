-- Prove2me | solution 1 for BKAR.Forest.grownForestForSupportOrder_branchIntegral_eq_orderedContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:35:33.783847+00:00
-- url     : https://prove2.me/submissions/21afe6a9-26d9-46b0-844b-e5cfa26db14a

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_emptyStart_eq_orderedContribution
import Theorems.Thm_BKAR_Forest_ChosenGrowth_branchIntegral_emptyStart_eq_orderedContribution
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_emptyStart_eq_orderedContribution


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
    (ρ : (Edge V → ℝ) → ℝ) :
  (grownForestForSupportOrder_orderedGrowth choices I order).branchIntegral
        emptyParam ρ =
      (grownForestForSupportOrder choices I order).orderedContribution
        order.val ρ :=
  OrderedGrowth.branchIntegral_emptyStart_eq_orderedContribution
    (grownForestForSupportOrder_orderedGrowth choices I order) ρ
end BKAR.Forest
