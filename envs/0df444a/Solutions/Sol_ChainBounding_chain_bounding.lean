-- Prove2me | solution 1 for ChainBounding.chain_bounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:48:03.359044+00:00
-- url     : https://prove2.me/submissions/337227b8-e2df-47ea-bb2c-39cae000822e

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_OrderExpander_ssubset_g
import Theorems.Thm_OrderExpander_IsSegment_U_of_Good
import Theorems.Thm_OrderExpander_greatest_good_chain
import Theorems.Thm_ChainBounding_ssubset_g
import Theorems.Thm_ChainBounding_Good_successor

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
noncomputable section
variable [PartialOrder α] [OrderSelector α] [ChainBounding α]
open OrderSelector OrderExpander
open ChainBounding
include α
namespace ChainBounding
theorem _root_.solution : False := by
  have goodU : Good U := greatest_good_chain (α := α)
  have Good_gU : Good (g U) := Good_successor U goodU
  have gnotsub : ¬(g U ⊆ U) := not_subset_of_ssubset $ ssubset_g goodU.1
  have : g U ⊆ U := (IsSegment_U_of_Good Good_gU).left
  exact gnotsub this
end ChainBounding
