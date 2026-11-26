-- Prove2me | solution 1 for BKAR.Forest.card_edgeOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:17.813442+00:00
-- url     : https://prove2.me/submissions/cdc26bb4-caa3-4698-a165-0357907819bd

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_card_edgeSetOrders

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) :
    F.edgeOrders.card = F.edges.card.factorial := by
  exact card_edgeSetOrders F.edges
end BKAR.Forest
