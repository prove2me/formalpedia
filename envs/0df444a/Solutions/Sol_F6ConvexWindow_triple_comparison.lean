-- Prove2me | solution 1 for F6ConvexWindow.triple_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:33:41.526369+00:00
-- url     : https://prove2.me/submissions/6fb9400b-871a-4d4c-a533-bef19fbf98db

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
theorem _root_.solution (hw : WidthLE (V := V) 3) {T : Finset V}
    (ht : Antichain T) (hc : T.card = 3) {x : V} (hx : x ∉ T) :
    ∃ y ∈ T, x ≤ y ∨ y ≤ x := by
  classical
  by_contra hn
  have hi : ∀ y ∈ T, IncRel x y := by
    intro y hy
    exact ⟨fun h => hn ⟨y, hy, Or.inl h⟩, fun h => hn ⟨y, hy, Or.inr h⟩⟩
  have ht' : Antichain (insert x T) := by
    intro a ha b hb hab
    rcases mem_insert.mp ha with rfl | haT
    · rcases mem_insert.mp hb with rfl | hbT
      · rfl
      · exact False.elim ((hi b hbT).1 hab)
    · rcases mem_insert.mp hb with rfl | hbT
      · exact False.elim ((hi a haT).2 hab)
      · exact ht a haT b hbT hab
  have := hw (insert x T) ht'
  rw [card_insert_of_notMem hx, hc] at this
  omega
end F6ConvexWindow
