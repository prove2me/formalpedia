-- Prove2me | solution 1 for BKAR.Forest.orderedSectorSum_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:40.886172+00:00
-- url     : https://prove2.me/submissions/fa17f017-d1e0-4dce-9ac5-9e8db34ae9c8

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_empty_edgeOrders
import Theorems.Thm_BKAR_Forest_orderedContribution_empty

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (ρ : (Edge V → ℝ) → ℝ) :
    (Forest.empty V).orderedSectorSum ρ = ρ zeroConfig := by
  rw [orderedSectorSum, empty_edgeOrders]
  rw [Finset.sum_singleton, orderedContribution_empty]
end BKAR.Forest
