-- Prove2me | solution 1 for GalvinMultigraph.Gadget.degree_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:47:02.700627+00:00
-- url     : https://prove2.me/submissions/d9ca7d2c-9569-4b0b-ba44-fe3b4e523c54

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_GalvinMultigraph_Gadget
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_aEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_bEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_innerEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_rowEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_neighbor_b_iff
attribute [local simp] GalvinMultigraph.Gadget.lists_aEdge
attribute [local simp] GalvinMultigraph.Gadget.lists_bEdge
attribute [local simp] GalvinMultigraph.Gadget.lists_innerEdge
attribute [local simp] GalvinMultigraph.Gadget.lists_rowEdge

set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph GalvinMultigraph.Gadget
open Finset SimpleGraph
variable {A B E Color : Type*} {k : ℕ} [NeZero k]
namespace GalvinMultigraph.Gadget
theorem _root_.solution [Fintype A] [Fintype B] [Fintype E]
    (a : E → A) (b : E → B) (y : B) :
    (graph (k := k) a b).degree (Sum.inr (Sum.inl y)) ≤
      Nat.card {e // b e = y} := by
  classical
  let f : (graph (k := k) a b).neighborSet (Sum.inr (Sum.inl y)) → {e // b e = y} :=
    fun v => ⟨((neighbor_b_iff a b y v.val).mp v.property).choose,
      ((neighbor_b_iff a b y v.val).mp v.property).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    have hv := ((neighbor_b_iff a b y v.val).mp v.property).choose_spec.2
    have hw := ((neighbor_b_iff a b y w.val).mp w.property).choose_spec.2
    have he : (f v).val = (f w).val := congrArg Subtype.val h
    change v.val = Sum.inl (Sum.inr ((f v).val, 0)) at hv
    change w.val = Sum.inl (Sum.inr ((f w).val, 0)) at hw
    rw [hv, hw, he]
  rw [← card_neighborSet_eq_degree, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective f hf
end GalvinMultigraph.Gadget
