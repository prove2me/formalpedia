-- Prove2me | solution 1 for Erdos654Proof.card_image_erase_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:51:54.894103+00:00
-- url     : https://prove2.me/submissions/9a1cae68-d85c-4f58-adbd-2a617594b079

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution [DecidableEq ℝ²] (S B C : Finset ℝ²) {x : ℝ²}
    (hS : ∀ y ∈ S, y ∈ B ∨ y ∈ C) (hx : x ∈ B) :
    #((S.erase x).image fun y ↦ dist y x) ≤ (#B - 1) + #(C.image fun y ↦ dist y x) := by
  have hsub : S.erase x ⊆ B.erase x ∪ C := by
    intro y hy
    rw [mem_erase] at hy
    rw [mem_union, mem_erase]
    rcases hS y hy.2 with h | h
    · exact Or.inl ⟨hy.1, h⟩
    · exact Or.inr h
  calc #((S.erase x).image fun y ↦ dist y x)
      ≤ #((B.erase x ∪ C).image fun y ↦ dist y x) := card_le_card (image_subset_image hsub)
    _ ≤ #((B.erase x).image fun y ↦ dist y x) + #(C.image fun y ↦ dist y x) := by
      rw [image_union]; exact card_union_le _ _
    _ ≤ #(B.erase x) + #(C.image fun y ↦ dist y x) := by
      gcongr; exact card_image_le
    _ = (#B - 1) + #(C.image fun y ↦ dist y x) := by rw [card_erase_of_mem hx]
end Erdos654Proof
