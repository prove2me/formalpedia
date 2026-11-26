-- Prove2me | solution 1 for BKAR.Forest.length_eq_card_of_mem_edgeSetOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:04:55.653926+00:00
-- url     : https://prove2.me/submissions/a1a2fc4c-2ec1-4e9a-b81c-c0b0e5b7002d

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeSetOrders
import Theorems.Thm_BKAR_Forest_nodup_of_mem_edgeSetOrders

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
    order.length = S.card := by
  have hset := toFinset_eq_of_mem_edgeSetOrders h
  have hnodup := nodup_of_mem_edgeSetOrders h
  rw [← hset]
  exact (List.toFinset_card_of_nodup hnodup).symm
end BKAR.Forest
