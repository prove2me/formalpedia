-- Prove2me | solution 1 for GalvinMultigraph.Gadget.maxDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:52:22.780458+00:00
-- url     : https://prove2.me/submissions/fae6d53f-a46c-47fa-8513-da802ef9ba29

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_GalvinMultigraph_Gadget
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_aEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_bEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_innerEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_lists_rowEdge
public import Theorems.Thm_GalvinMultigraph_Gadget_index_injective_left
public import Theorems.Thm_GalvinMultigraph_Gadget_index_injective_right
public import Theorems.Thm_GalvinMultigraph_Gadget_degree_a
public import Theorems.Thm_GalvinMultigraph_Gadget_degree_b
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
    (a : E → A) (b : E → B)
    (ha : ∀ x, Nat.card {e // a e = x} ≤ k)
    (hb : ∀ y, Nat.card {e // b e = y} ≤ k) : (graph (k := k) a b).maxDegree ≤ k := by
  classical
  apply (graph (k := k) a b).maxDegree_le_of_forall_degree_le k
  rintro ((x | ⟨e, i⟩) | (y | ⟨e, j⟩))
  · exact (degree_a a b x).trans (ha x)
  · rw [← card_neighborSet_eq_degree]
    simpa using Fintype.card_le_of_injective _ (index_injective_left a b e i)
  · exact (degree_b a b y).trans (hb y)
  · rw [← card_neighborSet_eq_degree]
    simpa using Fintype.card_le_of_injective _ (index_injective_right a b e j)
end GalvinMultigraph.Gadget
