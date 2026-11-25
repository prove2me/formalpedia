-- Prove2me | solution 1 for Galvin.colour_endB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:14.803197+00:00
-- url     : https://prove2.me/submissions/c9abf80a-f738-4be1-b1b5-4251e1d4aa3d

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
public import Definitions.Def_GalvinLib_Orientation
public import Theorems.Thm_Galvin_colour_endA
public import Theorems.Thm_Galvin_adj_ends

set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace Galvin
theorem _root_.solution (c : G.Coloring (Fin 2)) (e : G.edgeSet) : c (endB c e) = 1 := by
  have h1 := c.valid (adj_ends c e)
  rw [colour_endA] at h1
  revert h1
  generalize c (endB c e) = i
  revert i
  decide
end Galvin
