-- Prove2me | solution 1 for GalvinMultigraph.Gadget.index_injective_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:44:51.241385+00:00
-- url     : https://prove2.me/submissions/7b064250-ca3e-4c63-8e4f-9724c508cd28

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
theorem _root_.solution (a : E → A) (b : E → B) (e : E) (j : Fin k) :
    Function.Injective (fun v : (graph a b).neighborSet (Sum.inr (Sum.inr (e, j))) =>
      index v.val) := by
  rintro ⟨v, hv⟩ ⟨w, hw⟩ h
  apply Subtype.ext
  rcases v with (x | ⟨f, i⟩) | (y | ⟨f, i⟩) <;>
    rcases w with (x' | ⟨g, l⟩) | (y' | ⟨g, l⟩) <;>
    simp only [graph, cross] at hv hw <;>
    simp only [index] at h <;> aesop
end GalvinMultigraph.Gadget
