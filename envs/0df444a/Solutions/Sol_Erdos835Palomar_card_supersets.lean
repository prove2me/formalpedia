-- Prove2me | solution 1 for Erdos835Palomar.card_supersets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:12:35.221828+00:00
-- url     : https://prove2.me/submissions/e2af76d6-edb6-4d25-8445-a524175abc6d

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
public import Definitions.Def_Erdos835Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Erdos835Palomar
variable {α : Type*} [DecidableEq α]
namespace Erdos835Palomar
theorem _root_.solution (W s : Finset α) (hsW : s ⊆ W) :
    #((powersetCard (#s + 1) W).filter (fun A => s ⊂ A)) = #W - #s := by
  have himg : (powersetCard (#s + 1) W).filter (fun A => s ⊂ A) =
      (W \ s).image (fun x => insert x s) := by
    ext A
    simp only [mem_filter, mem_powersetCard, mem_image, mem_sdiff]
    constructor
    · rintro ⟨⟨hAW, hAc⟩, hsA⟩
      obtain ⟨a, ha, rfl⟩ := (Finset.exists_eq_insert_iff).mpr ⟨hsA.subset, hAc.symm⟩
      exact ⟨a, ⟨hAW (mem_insert_self a s), ha⟩, rfl⟩
    · rintro ⟨x, ⟨hxW, hxs⟩, rfl⟩
      exact ⟨⟨insert_subset hxW hsW, card_insert_of_notMem hxs⟩, ssubset_insert hxs⟩
  rw [himg, card_image_of_injOn, card_sdiff_of_subset hsW]
  intro x hx y hy hxy
  simp only [coe_sdiff, Set.mem_sdiff, mem_coe] at hx hy
  have hxy' : insert x s = insert y s := hxy
  have : x ∈ insert y s := hxy' ▸ mem_insert_self x s
  rcases mem_insert.mp this with h | h
  · exact h
  · exact absurd h hx.2
end Erdos835Palomar
