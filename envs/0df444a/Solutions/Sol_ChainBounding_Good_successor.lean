-- Prove2me | solution 1 for ChainBounding.Good_successor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:46:56.247155+00:00
-- url     : https://prove2.me/submissions/8bacfe61-30da-426f-97ce-f0e2c1043313

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_IsSegment_of_Subset
import Theorems.Thm_ChainBounding_subset_of_IsSegment_successor
import Theorems.Thm_ChainBounding_IsSegment_successor

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
noncomputable section
variable [PartialOrder α] [OrderSelector α] [ChainBounding α]
open OrderSelector OrderExpander
open ChainBounding
namespace ChainBounding
theorem _root_.solution (C : Set α) (goodC : Good C) : Good (g C) := by
  constructor
  · simp only [g, union_singleton]
    exact IsChain.insert goodC.1 fun b hbC _ => Or.inr (le_of_lt (strbds C goodC.1 b hbC))
  · intro S Sprseg
    have SsubC : S ⊆ C := @subset_of_IsSegment_successor _ _ _ _ _ _ ⟨goodC.1⟩ Sprseg
    have Cseg : IsSegment C (g C) := IsSegment_successor goodC.1
    have SsegC : IsSegment S C := IsSegment_of_Subset C (g C) _ Cseg.left Sprseg.1 SsubC
    rcases em (S = C) with rfl | SneqC
    · constructor <;> try rfl
      simp_all only []
    · constructor
      · exact (goodC.2 ⟨SsegC, SneqC⟩).1
      · calc
        g S ⊑ C   := (goodC.2 ⟨SsegC, SneqC⟩).2
        _   ⊑ g C := Cseg
end ChainBounding
