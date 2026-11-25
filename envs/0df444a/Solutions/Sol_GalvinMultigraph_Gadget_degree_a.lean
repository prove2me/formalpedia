-- Prove2me | solution 1 for GalvinMultigraph.Gadget.degree_a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:46:43.361802+00:00
-- url     : https://prove2.me/submissions/06df6792-5f5d-4601-a874-5a7798b01ecb

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_GalvinMultigraph_Gadget
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_aEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_bEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_innerEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_rowEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_neighbor_a_iff
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
    (a : E → A) (b : E → B) (x : A) :
    (graph (k := k) a b).degree (Sum.inl (Sum.inl x)) ≤
      Nat.card {e // a e = x} := by
  classical
  let f : (graph (k := k) a b).neighborSet (Sum.inl (Sum.inl x)) → {e // a e = x} :=
    fun v => ⟨((neighbor_a_iff a b x v.val).mp v.property).choose,
      ((neighbor_a_iff a b x v.val).mp v.property).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    have hv := ((neighbor_a_iff a b x v.val).mp v.property).choose_spec.2
    have hw := ((neighbor_a_iff a b x w.val).mp w.property).choose_spec.2
    have he : (f v).val = (f w).val := congrArg Subtype.val h
    change v.val = Sum.inr (Sum.inr ((f v).val, 0)) at hv
    change w.val = Sum.inr (Sum.inr ((f w).val, 0)) at hw
    rw [hv, hw, he]
  rw [← card_neighborSet_eq_degree, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective f hf
end GalvinMultigraph.Gadget
