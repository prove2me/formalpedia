-- Prove2me | solution 1 for GalvinMultigraph.Gadget.rowColor_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:46:27.136833+00:00
-- url     : https://prove2.me/submissions/47aa5ff9-66e7-438c-8b4a-a3f76978c72d

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_GalvinMultigraph_Gadget
public import Theorems.Thm_GalvinMultigraph_Gadget_rowEdge_injective
public import Theorems.Thm_GalvinMultigraph_Gadget_rowEdge_mem
public import Theorems.Thm_GalvinMultigraph_Gadget_edge_eq_of_color_eq

set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph GalvinMultigraph.Gadget
open Finset SimpleGraph
variable {A B E Color : Type*} {k : ℕ} [NeZero k]
namespace GalvinMultigraph.Gadget
theorem _root_.solution (a : E → A) (b : E → B)
    (col : (graph (k := k) a b).lineGraph.Coloring Color) (e : E) (i : Fin k) :
    Function.Injective (fun j => col (rowEdge a b e i j)) := by
  intro j j' h
  exact rowEdge_injective a b e i (edge_eq_of_color_eq col
    (rowEdge_mem a b e i j) (rowEdge_mem a b e i j') h)
end GalvinMultigraph.Gadget
