-- Prove2me | solution 1 for BKAR.Forest.rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:17.852892+00:00
-- url     : https://prove2.me/submissions/70010d21-f98a-4927-86d1-157dcff22f9a

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_chosenGrowth_eq_orderedContribution
import Theorems.Thm_P2M_BKAR_Forest_chosenGrowth_of_followOrder__eq_some_324c28c4883b


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    {G : Forest V} {order : List (Edge V)}
    (hG : followOrder? choices (Forest.empty V) order = some G)
    (ρ : (Edge V → ℝ) → ℝ)
    (horder : order ≠ []) :
    rootBoundarySupportOrderContribution choices ρ G.support order =
      G.orderedContribution order ρ :=
  rootBoundarySupportOrderContribution_chosenGrowth_eq_orderedContribution
    choices (chosenGrowth_of_followOrder?_eq_some choices hG) ρ horder
end BKAR.Forest
