-- Prove2me | solution 1 for Galvin.colour_endA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:02:48.963848+00:00
-- url     : https://prove2.me/submissions/b382ba10-bfa0-4bbf-a2fa-75a8f605233a

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
public import Definitions.Def_GalvinLib_Orientation

set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace Galvin
theorem _root_.solution (c : G.Coloring (Fin 2)) (e : G.edgeSet) : c (endA c e) = 0 :=
  (exists_ends c e).choose_spec.choose_spec.2
end Galvin
