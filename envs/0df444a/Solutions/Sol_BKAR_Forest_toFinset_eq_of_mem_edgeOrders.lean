-- Prove2me | solution 1 for BKAR.Forest.toFinset_eq_of_mem_edgeOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:50:08.074009+00:00
-- url     : https://prove2.me/submissions/e67a29bc-2ad9-4f62-9d1c-138887b3d5d9

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_mem_edgeOrders_iff_toFinset_eq_and_nodup

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    {order : List (Edge V)} (h : order ∈ F.edgeOrders) :
    order.toFinset = F.edges :=
  ((F.mem_edgeOrders_iff_toFinset_eq_and_nodup).mp h).1
end BKAR.Forest
