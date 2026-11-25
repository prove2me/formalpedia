-- Prove2me | solution 1 for GalvinMultigraph.Gadget.columnColor_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:47:05.883588+00:00
-- url     : https://prove2.me/submissions/9987d16e-5013-42ce-ba42-731b843a6071

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_GalvinMultigraph_Gadget
public import Theorems.Thm_GalvinMultigraph_Gadget_columnEdge_injective
public import Theorems.Thm_GalvinMultigraph_Gadget_columnEdge_mem
public import Theorems.Thm_GalvinMultigraph_Gadget_edge_eq_of_color_eq

set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph GalvinMultigraph.Gadget
open Finset SimpleGraph
variable {A B E Color : Type*} {k : ℕ} [NeZero k]
namespace GalvinMultigraph.Gadget
theorem _root_.solution (a : E → A) (b : E → B)
    (col : (graph (k := k) a b).lineGraph.Coloring Color) (e : E) (j : Fin k) (hj : j ≠ 0) :
    Function.Injective (fun i => col (rowEdge a b e i j)) := by
  intro i i' h
  exact columnEdge_injective a b e j hj (edge_eq_of_color_eq col
    (columnEdge_mem a b e i j hj) (columnEdge_mem a b e i' j hj) h)
end GalvinMultigraph.Gadget
