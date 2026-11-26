-- Prove2me | solution 1 for BKAR.Forest.mem_edgeOrders_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:45.942192+00:00
-- url     : https://prove2.me/submissions/fd3a65e2-0ed1-4618-b1aa-c7b3a143f762

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrders_iff

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) {order : List (Edge V)} :
    order ∈ F.edgeOrders ↔ order.Perm F.edges.toList := by
  exact mem_edgeSetOrders_iff F.edges
end BKAR.Forest
