-- Prove2me | solution 1 for GalvinMultigraph.Gadget.neighbor_b_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:35.080122+00:00
-- url     : https://prove2.me/submissions/977cc3f9-bc15-49d4-a179-a26fdf55afe8

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
theorem _root_.solution (a : E → A) (b : E → B) (y : B) (v : Vertex A B E k) :
    (graph a b).Adj (Sum.inr (Sum.inl y)) v ↔
      ∃ e, b e = y ∧ v = Sum.inl (Sum.inr (e, 0)) := by
  rcases v with (x | ⟨e, i⟩) | (x | ⟨e, i⟩) <;>
    simp [graph, cross, eq_comm]
end GalvinMultigraph.Gadget
