-- Prove2me | solution 1 for GalvinMultigraph.Gadget.lists_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:45:27.675119+00:00
-- url     : https://prove2.me/submissions/5e9908f9-db5d-4792-8df5-9ddcc268d32c

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
theorem _root_.solution (a : E → A) (b : E → B) (P : E → Finset Color)
    (hP : ∀ e, (P e).card = k) (f : (graph (k := k) a b).edgeSet) :
    (lists a b P f).card = k := by
  classical
  obtain ⟨f, hf⟩ := f
  induction f using Sym2.ind with
  | _ u v =>
    change (graph a b).Adj u v at hf
    change (tagList P (tag u) (tag v)).card = k
    rcases u with (x | ⟨e, i⟩) | (y | ⟨e, i⟩) <;>
      rcases v with (x' | ⟨f, j⟩) | (y' | ⟨f, j⟩) <;>
      simp_all [graph, cross, tagList, tag]
end GalvinMultigraph.Gadget
