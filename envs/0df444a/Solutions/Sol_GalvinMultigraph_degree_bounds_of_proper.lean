-- Prove2me | solution 1 for GalvinMultigraph.degree_bounds_of_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:52:16.806809+00:00
-- url     : https://prove2.me/submissions/ed65d1c9-918f-4f5a-99a6-a699ed3ed465

module
public import Definitions.Def_GalvinMultigraph_Gadget
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinMultigraph_Main
public import Theorems.Thm_LeanPool_Vizing_PEC_Extends_trans


set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph
open Finset
variable {A B E Color : Type*}
namespace GalvinMultigraph
theorem _root_.solution [Finite E] [Fintype Color]
    (a : E → A) (b : E → B) (c : E → Color) (hc : Proper a b c) :
    (∀ x, Nat.card {e // a e = x} ≤ Fintype.card Color) ∧
    (∀ y, Nat.card {e // b e = y} ≤ Fintype.card Color) := by
  classical
  let _ := Fintype.ofFinite E
  constructor
  · intro x
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_le_of_injective (fun e : {e // a e = x} => c e.val)
    intro e f h
    apply Subtype.ext
    by_contra hne
    exact hc e.val f.val hne (Or.inl (e.property.trans f.property.symm)) h
  · intro y
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_le_of_injective (fun e : {e // b e = y} => c e.val)
    intro e f h
    apply Subtype.ext
    by_contra hne
    exact hc e.val f.val hne (Or.inr (e.property.trans f.property.symm)) h
end GalvinMultigraph
