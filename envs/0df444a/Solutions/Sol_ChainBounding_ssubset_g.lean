-- Prove2me | solution 1 for ChainBounding.ssubset_g
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:46:30.39954+00:00
-- url     : https://prove2.me/submissions/b83a5bf6-2adc-4518-9ee3-470593f8b979

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_ChainBounding_not_mem_f

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
noncomputable section
variable [PartialOrder α] [OrderSelector α] [ChainBounding α]
open OrderSelector OrderExpander
open ChainBounding
namespace ChainBounding
theorem _root_.solution {C : Set α} (hC : IsChain (· ≤ ·) C) : C ⊂ g C := by
  apply ssubset_of_ne_of_subset
  · exact (fun h => not_mem_f hC $ Eq.subset h.symm $ mem_union_right C rfl)
  · exact subset_union_left
end ChainBounding
