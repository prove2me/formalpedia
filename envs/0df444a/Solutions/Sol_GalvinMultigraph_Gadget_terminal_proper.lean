-- Prove2me | solution 1 for GalvinMultigraph.Gadget.terminal_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:53:52.207538+00:00
-- url     : https://prove2.me/submissions/ea35498b-375c-425c-a976-32ae901d2c28

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_GalvinMultigraph_Gadget
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_aEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_bEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_innerEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_rowEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_edge_eq_of_color_eq
public import Theorems.Thm_GalvinMultigraph_Gadget_aEdge_injective
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
theorem _root_.solution (a : E → A) (b : E → B)
    (col : (graph (k := k) a b).lineGraph.Coloring Color)
    (heq : ∀ e, col (aEdge a b e) = col (bEdge a b e)) :
    ∀ e f, e ≠ f → a e = a f ∨ b e = b f → col (aEdge a b e) ≠ col (aEdge a b f) := by
  intro e f hne hends hcol
  rcases hends with ha | hb
  · have h := edge_eq_of_color_eq col (v := Sum.inl (Sum.inl (a e)))
      (by simp [aEdge]) (by simp [aEdge, ha]) hcol
    exact hne (aEdge_injective a b h)
  · rw [heq e, heq f] at hcol
    have h := edge_eq_of_color_eq col (v := Sum.inr (Sum.inl (b e)))
      (by simp [bEdge]) (by simp [bEdge, hb]) hcol
    have hval : e = f ∧ b e = b f := by
      simpa [bEdge] using congrArg Subtype.val h
    exact hne hval.1
end GalvinMultigraph.Gadget
