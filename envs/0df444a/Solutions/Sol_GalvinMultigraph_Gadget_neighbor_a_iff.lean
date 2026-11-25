-- Prove2me | solution 1 for GalvinMultigraph.Gadget.neighbor_a_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:26.087298+00:00
-- url     : https://prove2.me/submissions/5e663a91-9712-4cf6-8022-8d1ede9b9834

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_GalvinMultigraph_Gadget
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_aEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_bEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_innerEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_rowEdge
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
theorem _root_.solution (a : E → A) (b : E → B) (x : A) (v : Vertex A B E k) :
    (graph a b).Adj (Sum.inl (Sum.inl x)) v ↔
      ∃ e, a e = x ∧ v = Sum.inr (Sum.inr (e, 0)) := by
  rcases v with (y | ⟨e, i⟩) | (y | ⟨e, i⟩) <;>
    simp [graph, cross, eq_comm]
end GalvinMultigraph.Gadget
