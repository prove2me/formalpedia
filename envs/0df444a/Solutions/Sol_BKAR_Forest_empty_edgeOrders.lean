-- Prove2me | solution 1 for BKAR.Forest.empty_edgeOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:26:25.035658+00:00
-- url     : https://prove2.me/submissions/4ab4d588-e81a-42f0-a710-b26fe36cb18c

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_edgeSetOrders_empty
import Theorems.Thm_BKAR_Forest_empty_edges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution :
    (Forest.empty V).edgeOrders = {[]} := by
  rw [edgeOrders, Forest.empty_edges V, edgeSetOrders_empty]
end BKAR.Forest
