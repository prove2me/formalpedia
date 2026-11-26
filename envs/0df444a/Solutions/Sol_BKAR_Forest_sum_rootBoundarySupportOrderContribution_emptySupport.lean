-- Prove2me | solution 1 for BKAR.Forest.sum_rootBoundarySupportOrderContribution_emptySupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:34:47.768829+00:00
-- url     : https://prove2.me/submissions/4f543dd6-c64f-4f19-ab5d-a0b3753de878

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
import Theorems.Thm_BKAR_Forest_edgeSetOrders_empty
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (edgeSetOrders (Forest.empty V).support.edges)
        (fun order =>
          rootBoundarySupportOrderContribution choices ρ
            (Forest.empty V).support order) =
      (Forest.empty V).orderedContribution [] ρ := by
  rw [show (Forest.empty V).support.edges = (∅ : Finset (Edge V)) by rfl]
  rw [edgeSetOrders_empty, Finset.sum_singleton]
  exact
    rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
      choices ρ (Forest.empty V).support rfl
end BKAR.Forest
