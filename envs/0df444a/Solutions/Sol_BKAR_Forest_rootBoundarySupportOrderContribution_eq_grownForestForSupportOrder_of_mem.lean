-- Prove2me | solution 1 for BKAR.Forest.rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:35:20.060971+00:00
-- url     : https://prove2.me/submissions/e2dafc65-1bf3-40b8-9eb7-044f7d090a09

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) {order : List (Edge V)}
    (horder : order ∈ edgeSetOrders I.edges)
    (ρ : (Edge V → ℝ) → ℝ) :
    rootBoundarySupportOrderContribution choices ρ I order =
      (grownForestForSupportOrder choices I ⟨order, horder⟩).orderedContribution
        order ρ :=
  rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder
    choices I ⟨order, horder⟩ ρ
end BKAR.Forest
