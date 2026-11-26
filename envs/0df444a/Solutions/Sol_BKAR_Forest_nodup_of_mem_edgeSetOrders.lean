-- Prove2me | solution 1 for BKAR.Forest.nodup_of_mem_edgeSetOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:03:38.232317+00:00
-- url     : https://prove2.me/submissions/fe078cfa-7f3f-4d21-bcd0-8353de295537

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
    order.Nodup :=
  ((mem_edgeSetOrders_iff_toFinset_eq_and_nodup S).mp h).2
end BKAR.Forest
