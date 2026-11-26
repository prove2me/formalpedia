-- Prove2me | solution 1 for BKAR.Forest.sum_rootBoundarySupportOrderContribution_eq_sum_grownForestForSupportOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:37.203868+00:00
-- url     : https://prove2.me/submissions/ad257932-b4f2-4286-bfa0-152d33a6b382

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
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (edgeSetOrders I.edges)
        (fun order =>
          rootBoundarySupportOrderContribution choices ρ I order) =
      Finset.sum (edgeSetOrders I.edges).attach
        (fun order =>
          (grownForestForSupportOrder choices I order).orderedContribution
            order.val ρ) := by
  rw [← (edgeSetOrders I.edges).sum_attach
    (fun order => rootBoundarySupportOrderContribution choices ρ I order)]
  apply Finset.sum_congr rfl
  intro order _
  exact
    rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder
      choices I order ρ
end BKAR.Forest
