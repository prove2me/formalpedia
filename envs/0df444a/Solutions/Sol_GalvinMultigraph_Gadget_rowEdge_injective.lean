-- Prove2me | solution 1 for GalvinMultigraph.Gadget.rowEdge_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:38:53.830523+00:00
-- url     : https://prove2.me/submissions/dcbada65-4e00-4129-8174-d47571ffeea5

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
theorem _root_.solution (a : E → A) (b : E → B) (e : E) (i : Fin k) :
    Function.Injective (rowEdge a b e i) := by
  intro j j' h
  have hval := congrArg Subtype.val h
  unfold rowEdge at hval
  split_ifs at hval with h h'
  · exact h.2.trans h'.2.symm
  · simp [bEdge, innerEdge] at hval
  · simp [bEdge, innerEdge] at hval
  · simpa [innerEdge] using hval
end GalvinMultigraph.Gadget
