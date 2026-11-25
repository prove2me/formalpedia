-- Prove2me | solution 1 for Erdos835Palomar.card_color_in
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:17:00.2347+00:00
-- url     : https://prove2.me/submissions/b0965ac7-bbfb-4c1b-8424-1c372f64d316

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
public import Definitions.Def_Erdos835Palomar_Solution
public import Theorems.Thm_Erdos835Palomar_card_ssubsets

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Erdos835Palomar
variable {α : Type*} [DecidableEq α]
variable {k : ℕ}
namespace Erdos835Palomar
theorem _root_.solution (c : {s : Finset (Fin (2 * k)) // #s = k} → Fin (k + 1))
    (hc : ∀ A : Finset (Fin (2 * k)), #A = k + 1 → image c {s | s.val ⊂ A} = univ)
    (A : Finset (Fin (2 * k))) (hA : #A = k + 1) (i : Fin (k + 1)) :
    #({s | s.val ⊂ A ∧ c s = i} : Finset {s : Finset (Fin (2 * k)) // #s = k}) = 1 := by
  set T : Finset {s : Finset (Fin (2 * k)) // #s = k} := {s | s.val ⊂ A} with hTdef
  have hinj : Set.InjOn c T := by
    rw [← card_image_iff, hc A hA, card_univ, Fintype.card_fin, card_ssubsets hA]
  have hfilt : ({s | s.val ⊂ A ∧ c s = i} : Finset {s : Finset (Fin (2 * k)) // #s = k}) =
      T.filter (fun s => c s = i) := by
    ext s; simp [hTdef]
  rw [hfilt, card_eq_one]
  have hi : i ∈ image c T := by rw [hc A hA]; exact mem_univ i
  obtain ⟨s, hsT, hsi⟩ := mem_image.mp hi
  refine ⟨s, ?_⟩
  ext t
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨htT, hti⟩
    exact hinj htT hsT (hti.trans hsi.symm)
  · rintro rfl
    exact ⟨hsT, hsi⟩
end Erdos835Palomar
