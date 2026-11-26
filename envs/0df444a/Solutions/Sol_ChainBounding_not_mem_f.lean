-- Prove2me | solution 1 for ChainBounding.not_mem_f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:46:03.305234+00:00
-- url     : https://prove2.me/submissions/b02e9c2a-552e-4427-bb06-50456f58da51

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
theorem _root_.solution {C : Set α} (hC : IsChain (· ≤ ·) C) : f C ∉ C := by
  have : ∀ c ∈ C, c ≠ f C := fun c (h : c ∈ C) => ne_of_lt <| strbds C hC c h
  tauto
end ChainBounding
