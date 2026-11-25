-- Prove2me | solution 1 for Galvin.eq_of_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:03:44.279226+00:00
-- url     : https://prove2.me/submissions/d4bdb2f7-c0fe-4ecb-a0c1-47e51f20ccbb

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
public import Definitions.Def_GalvinLib_Orientation
public import Theorems.Thm_Galvin_edge_eq_ends

set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace Galvin
theorem _root_.solution (c : G.Coloring (Fin 2)) {e f : G.edgeSet} (hA : endA c e = endA c f)
    (hB : endB c e = endB c f) : e = f := by
  apply Subtype.ext
  rw [edge_eq_ends c e, edge_eq_ends c f, hA, hB]
end Galvin
