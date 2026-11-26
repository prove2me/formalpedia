-- Prove2me | solution 1 for BKAR.Forest.toFinset_eq_of_mem_edgeSetOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:49:07.852839+00:00
-- url     : https://prove2.me/submissions/0909fddc-2816-4c5b-93cf-e5182def5d95

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
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution
    {S : Finset (Edge V)} {order : List (Edge V)}
    (h : order ∈ edgeSetOrders S) :
    order.toFinset = S :=
  ((mem_edgeSetOrders_iff_toFinset_eq_and_nodup S).mp h).1
end BKAR.Forest
