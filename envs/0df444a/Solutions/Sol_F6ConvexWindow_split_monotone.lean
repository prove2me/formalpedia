-- Prove2me | solution 1 for F6ConvexWindow.split_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:34:13.527073+00:00
-- url     : https://prove2.me/submissions/7a8503df-0d1c-400d-a627-4e2ec77cadd8

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_above_not_le
import Theorems.Thm_F6ConvexWindow_below_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_triple_split
attribute [local simp] F6ConvexWindow.mem_ideal



set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T)
    (hST : ideal S ⊆ ideal T) {x : V} (hxS : x ∉ S) (hxT : x ∉ T) :
    (Above T x → Above S x) ∧ (Below S x → Below T x) := by
  have hincompat : Below S x → Above T x → False := by
    intro hl hu
    obtain ⟨t, htT, hxt⟩ := mem_ideal.mp (hST (below_mem_ideal hl))
    exact above_not_le ht.1 hu htT hxt
  constructor
  · intro hu
    exact (triple_split hw hci hs.1 hs.2 hxS).resolve_left (fun hl => hincompat hl hu)
  · intro hl
    exact (triple_split hw hci ht.1 ht.2 hxT).resolve_right (hincompat hl)
end F6ConvexWindow
