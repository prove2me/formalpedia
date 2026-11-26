-- Prove2me | solution 1 for BKAR.Forest.length_eq_card_of_mem_edgeOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:05.782143+00:00
-- url     : https://prove2.me/submissions/5fafad30-5742-48aa-8fe7-37838336aeb9

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_length_eq_card_of_mem_edgeSetOrders

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    {order : List (Edge V)} (h : order ∈ F.edgeOrders) :
    order.length = F.edges.card := by
  exact length_eq_card_of_mem_edgeSetOrders h
end BKAR.Forest
