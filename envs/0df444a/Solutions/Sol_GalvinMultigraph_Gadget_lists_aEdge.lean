-- Prove2me | solution 1 for GalvinMultigraph.Gadget.lists_aEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:37:46.480309+00:00
-- url     : https://prove2.me/submissions/bcfc668d-cbce-41a0-8586-ff99adf18eb4

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
theorem _root_.solution (a : E → A) (b : E → B) (P : E → Finset Color) (e : E) :
    lists a b P (aEdge (k := k) a b e) = P e := rfl
end GalvinMultigraph.Gadget
