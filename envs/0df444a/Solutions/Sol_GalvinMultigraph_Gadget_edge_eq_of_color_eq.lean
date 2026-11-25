-- Prove2me | solution 1 for GalvinMultigraph.Gadget.edge_eq_of_color_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:41:30.665813+00:00
-- url     : https://prove2.me/submissions/9c99784f-ff5d-4adb-927c-19d790749a7d

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_GalvinMultigraph_Gadget

set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph GalvinMultigraph.Gadget
open Finset SimpleGraph
variable {A B E Color : Type*} {k : ℕ} [NeZero k]
namespace GalvinMultigraph.Gadget
theorem _root_.solution {V : Type*} {H : SimpleGraph V}
    (col : H.lineGraph.Coloring Color) {f g : H.edgeSet} {v : V}
    (hf : v ∈ f.val) (hg : v ∈ g.val) (hc : col f = col g) : f = g := by
  by_contra hne
  exact col.valid (SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne, v, hf, hg⟩) hc
end GalvinMultigraph.Gadget
