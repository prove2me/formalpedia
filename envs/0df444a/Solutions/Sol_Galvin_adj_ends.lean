-- Prove2me | solution 1 for Galvin.adj_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:37:54.96075+00:00
-- url     : https://prove2.me/submissions/cd11a9dd-bbcb-4a30-8e25-7b33a5932d85

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
theorem _root_.solution (c : G.Coloring (Fin 2)) (e : G.edgeSet) : G.Adj (endA c e) (endB c e) := by
  have := e.2
  rw [edge_eq_ends c e] at this
  exact this
end Galvin
