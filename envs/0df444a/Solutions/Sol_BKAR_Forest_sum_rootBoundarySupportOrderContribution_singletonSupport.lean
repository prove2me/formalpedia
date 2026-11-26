-- Prove2me | solution 1 for BKAR.Forest.sum_rootBoundarySupportOrderContribution_singletonSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:34:49.364619+00:00
-- url     : https://prove2.me/submissions/2c4f0925-33c2-48a0-8d5f-398adb335a05

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
import Theorems.Thm_BKAR_ForestIndex_singleton_edges
import Theorems.Thm_BKAR_Forest_edgeSetOrders_singleton
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_singleton_eq_orderedContribution


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (edgeSetOrders (ForestIndex.singleton a : ForestIndex V).edges)
        (fun order =>
          rootBoundarySupportOrderContribution choices ρ
            (ForestIndex.singleton a) order) =
      (choices (Forest.empty V) (emptyActiveEdge a)).forest.orderedContribution
        [a] ρ := by
  rw [ForestIndex.singleton_edges, edgeSetOrders_singleton]
  rw [Finset.sum_singleton]
  exact rootBoundarySupportOrderContribution_singleton_eq_orderedContribution
    choices a ρ
end BKAR.Forest
