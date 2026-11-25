-- Prove2me | solution 1 for F6ConvexWindow.below_lt_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:32:25.279207+00:00
-- url     : https://prove2.me/submissions/01ab832c-ef33-460c-b5d2-5e6a80618db8

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution {T : Finset V} (hc : T.card = 3) {l u : V}
    (hl : Below T l) (hu : Above T u) : l < u := by
  classical
  let A := T.filter (fun t => l < t)
  let B := T.filter (fun t => t < u)
  have hun : A ∪ B ⊆ T := union_subset (filter_subset _ _) (filter_subset _ _)
  have hcard := card_le_card hun
  have hsum := card_union_add_card_inter A B
  have hpos : 0 < (A ∩ B).card := by
    change 2 ≤ A.card at hl
    change 2 ≤ B.card at hu
    omega
  obtain ⟨t, ht⟩ := card_pos.mp hpos
  obtain ⟨htA, htB⟩ := mem_inter.mp ht
  exact (mem_filter.mp htA).2.trans (mem_filter.mp htB).2
end F6ConvexWindow
