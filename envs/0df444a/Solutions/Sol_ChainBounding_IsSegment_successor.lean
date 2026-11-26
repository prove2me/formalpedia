-- Prove2me | solution 1 for ChainBounding.IsSegment_successor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:46:04.369125+00:00
-- url     : https://prove2.me/submissions/32ac4422-be72-41a2-80f1-c339455a7152

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
namespace ChainBounding
theorem _root_.solution {C : Set α} (chain : IsChain (· ≤ ·) C) : IsSegment C (g C) := by
  constructor
  · simp_all only [g, union_singleton, subset_insert]
  · intro c hc s hs cles
    rcases hc with cinC | hc
    · exact cinC
    · have : s < c := by rw [hc] ; exact strbds C chain s hs
      exfalso; exact lt_irrefl c (lt_of_le_of_lt cles this)
end ChainBounding
