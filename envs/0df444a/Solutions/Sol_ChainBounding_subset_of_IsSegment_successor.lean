-- Prove2me | solution 1 for ChainBounding.subset_of_IsSegment_successor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:46:32.121015+00:00
-- url     : https://prove2.me/submissions/c5a917d7-3cf9-4ed4-abcb-0da72238df7f

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_ChainBounding_eq_of_IsSegment_of_mem_top

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
noncomputable section
variable [PartialOrder α] [OrderSelector α] [ChainBounding α]
open OrderSelector OrderExpander
open ChainBounding
namespace ChainBounding
theorem _root_.solution {C S : Set α} [Chain C] (Sprseg : S ⊏ (g C)) : S ⊆ C := by
  have : ((⊤ : g C) : α) ∈ S → S = g C := eq_of_IsSegment_of_mem_top Sprseg.1
  have : f C ∉ S := fun a => Sprseg.2 (this a)
  intro s sinS
  rcases Sprseg.1.1 sinS with h | _
  · exact h
  · simp_all only [mem_singleton_iff]
end ChainBounding
