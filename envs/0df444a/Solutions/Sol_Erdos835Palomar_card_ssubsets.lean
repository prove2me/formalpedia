-- Prove2me | solution 1 for Erdos835Palomar.card_ssubsets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:12:06.399193+00:00
-- url     : https://prove2.me/submissions/5c5450a7-ce58-4a8f-90e1-af2b2a237342

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
variable {k : ℕ}
namespace Erdos835Palomar
theorem _root_.solution {A : Finset (Fin (2 * k))} (hA : #A = k + 1) :
    #({s | s.val ⊂ A} : Finset {s : Finset (Fin (2 * k)) // #s = k}) = k + 1 := by
  have hmap : ({s | s.val ⊂ A} : Finset {s : Finset (Fin (2 * k)) // #s = k}).map
      ⟨Subtype.val, Subtype.val_injective⟩ = powersetCard k A := by
    ext B
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk,
      mem_powersetCard]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hs.subset, s.2⟩
    · rintro ⟨hBA, hBc⟩
      refine ⟨⟨B, hBc⟩, ssubset_of_subset_of_ne hBA ?_, rfl⟩
      intro h
      have h' : B = A := h
      rw [h'] at hBc
      omega
  rw [← card_map ⟨Subtype.val, Subtype.val_injective⟩, hmap, card_powersetCard, hA]
  simp
end Erdos835Palomar
