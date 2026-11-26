-- Prove2me | solution 1 for BKAR.Forest.exists_sum_rootBoundarySupportOrderContribution_eq_orderedContribution_of_mem_edgeSetOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:34:34.11384+00:00
-- url     : https://prove2.me/submissions/28c679b8-8852-4629-a6fa-e22baa324efd

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
import Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
import Theorems.Thm_P2M_BKAR_Forest_exists_followOrder__eq_some_support_of_mem_edgeSetOrders_94b5d7b04ff1


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    {I : ForestIndex V} {order : List (Edge V)}
    (horder : order ∈ edgeSetOrders I.edges)
    (ρ : (Edge V → ℝ) → ℝ) :
    ∃ G : Forest V, G.support = I ∧
      Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun J => rootBoundarySupportOrderContribution choices ρ J order) =
        G.orderedContribution order ρ := by
  rcases exists_followOrder?_eq_some_support_of_mem_edgeSetOrders
      choices horder with
    ⟨G, hfollow, hsupport⟩
  refine ⟨G, hsupport, ?_⟩
  exact
    sum_rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
      choices hfollow ρ
end BKAR.Forest
