-- Prove2me | solution 1 for BKAR.Forest.mem_edgeOrders_iff_toFinset_eq_and_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:49:06.994875+00:00
-- url     : https://prove2.me/submissions/11bae802-5a31-494b-a2b6-ef215d7004ed

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrders_iff_toFinset_eq_and_nodup

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {order : List (Edge V)} :
    order ∈ F.edgeOrders ↔ order.toFinset = F.edges ∧ order.Nodup := by
  exact mem_edgeSetOrders_iff_toFinset_eq_and_nodup F.edges
end BKAR.Forest
