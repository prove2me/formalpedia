-- Prove2me | solution 1 for GalvinMultigraph.Gadget.lists_bEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:37:47.28133+00:00
-- url     : https://prove2.me/submissions/d6620573-6881-4024-9d33-7d5609635607

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
    lists a b P (bEdge (k := k) a b e) = P e := rfl
end GalvinMultigraph.Gadget
