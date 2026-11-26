-- Prove2me | solution 1 for BKAR.Forest.sum_rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:25.913374+00:00
-- url     : https://prove2.me/submissions/2e6f6b6b-00a5-480f-9249-5d406bc24728

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
import Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_chosenGrowth
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
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I order) =
      G.orderedContribution order ρ :=
  sum_rootBoundarySupportOrderContribution_chosenGrowth choices
    (chosenGrowth_of_followOrder?_eq_some choices hG) ρ
end BKAR.Forest
