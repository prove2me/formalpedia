-- Prove2me | solution 1 for Erdos657Proof.distinctDistances_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:28:50.513309+00:00
-- url     : https://prove2.me/submissions/7c187cfb-081e-4676-b699-1b090767ebfe

module
public import Mathlib
public import Definitions.Def_Erdos657Palomar_Solution
public import Theorems.Thm_Erdos657Proof_dist_pt

set_option autoImplicit true
@[expose] public section
public section
open scoped Finset
open Filter
open scoped EuclideanGeometry
open Erdos657Proof
open Finset
namespace Erdos657Proof
theorem _root_.solution (k : ℕ) : distinctDistances (univ.image pt : Finset (ℝ^k)) ≤ 2 ^ k - 1 := by
  unfold distinctDistances distanceSet
  have hsub : (univ.image pt : Finset (ℝ^k)).offDiag.image
      (fun pair : (ℝ^k) × (ℝ^k) ↦ dist pair.1 pair.2) ⊆
      (univ.erase ∅).image fun U : Finset (Fin k) ↦ Real.sqrt (g U) := by
    intro d hd
    rw [mem_image] at hd
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hd
    rw [mem_offDiag] at hxy
    obtain ⟨hx, hy, hne⟩ := hxy
    obtain ⟨S, -, rfl⟩ := mem_image.1 hx
    obtain ⟨T, -, rfl⟩ := mem_image.1 hy
    refine mem_image.2 ⟨symmDiff S T, mem_erase.2 ⟨fun h ↦ hne ?_, mem_univ _⟩, (dist_pt S T).symm⟩
    rw [← bot_eq_empty, symmDiff_eq_bot] at h
    rw [h]
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_finset, Fintype.card_fin]
end Erdos657Proof
