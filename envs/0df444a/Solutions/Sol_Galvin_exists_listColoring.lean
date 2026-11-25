-- Prove2me | solution 1 for Galvin.exists_listColoring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:41:39.603384+00:00
-- url     : https://prove2.me/submissions/d31518f1-f39a-4bdb-9549-9d068ae50392

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Definitions.Def_GalvinLib_Kernel
public import Theorems.Thm_Galvin_exists_listColoring_on

set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset
namespace Galvin
theorem _root_.solution {α Color : Type*} [Fintype α]
    (G : SimpleGraph α) (D : α → α → Prop) [DecidableRel D] (hK : HasKernels G D)
    (L : α → Finset Color)
    (hL : ∀ x, (Finset.univ.filter (D x ·)).card < (L x).card) :
    ∃ c : G.Coloring Color, ∀ x, c x ∈ L x := by
  classical
  cases isEmpty_or_nonempty α with
  | inl _ => exact ⟨SimpleGraph.Coloring.mk (fun x => isEmptyElim x) fun {x} => isEmptyElim x,
      fun x => isEmptyElim x⟩
  | inr hα => ?_
  have : Nonempty Color := by
    obtain ⟨x⟩ := hα
    obtain ⟨k, -⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (hL x))
    exact ⟨k⟩
  obtain ⟨c, hcL, hcp⟩ := exists_listColoring_on G D hK _ Finset.univ rfl L
    (fun x _ => hL x)
  exact ⟨SimpleGraph.Coloring.mk c fun {x y} h => hcp x (mem_univ _) y (mem_univ _) h,
    fun x => hcL x (mem_univ _)⟩
end Galvin
