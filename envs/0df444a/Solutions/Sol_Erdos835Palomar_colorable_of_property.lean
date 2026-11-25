-- Prove2me | solution 1 for Erdos835Palomar.colorable_of_property
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:17:01.458012+00:00
-- url     : https://prove2.me/submissions/dea3be3b-0d7c-48d3-8ed9-15af533010ee

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
theorem _root_.solution (hP : Property k) : J(2 * k, k).Colorable (k + 1) := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨Coloring.mk c ?_⟩
  intro s t hadj hct
  have hk : #(s.val ∩ t.val) + 1 = k := hadj
  have hst : s ≠ t := J(2 * k, k).ne_of_adj hadj
  have hU := card_union_add_card_inter s.val t.val
  rw [s.2, t.2] at hU
  have hA : #(s.val ∪ t.val) = k + 1 := by omega
  have hinj : Set.InjOn c ({u | u.val ⊂ s.val ∪ t.val} :
      Finset {s : Finset (Fin (2 * k)) // #s = k}) := by
    rw [← card_image_iff, hc _ hA, card_univ, Fintype.card_fin, card_ssubsets hA]
  have hsub : ∀ u : {s : Finset (Fin (2 * k)) // #s = k},
      u.val ⊆ s.val ∪ t.val → u.val ⊂ s.val ∪ t.val :=
    fun u hu => ssubset_of_subset_of_ne hu (fun h => by have := u.2; rw [h] at this; omega)
  refine hst (hinj ?_ ?_ hct)
  · simpa using hsub s subset_union_left
  · simpa using hsub t subset_union_right
end Erdos835Palomar
