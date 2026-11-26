-- Prove2me | solution 1 for ChainBounding.eq_of_IsSegment_of_mem_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:46:03.852788+00:00
-- url     : https://prove2.me/submissions/7fef3dec-b3d9-4794-9d73-04e1ea193bcd

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
noncomputable section
variable [PartialOrder α] [OrderSelector α] [ChainBounding α]
open OrderSelector OrderExpander
open ChainBounding
omit [OrderSelector α] [ChainBounding α]
namespace ChainBounding
theorem _root_.solution {C S : Set α} [OrderTop ↑C] (Sseg : IsSegment S C)
    (topin : ((⊤ : C) : α) ∈ S) : S = C := by
  apply eq_of_subset_of_subset Sseg.1
  intro c cinC
  have : (⟨c,cinC⟩ : C) ≤ ⊤ := le_top
  exact Sseg.2 c cinC _ topin this
end ChainBounding
