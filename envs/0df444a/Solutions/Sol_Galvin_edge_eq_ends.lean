-- Prove2me | solution 1 for Galvin.edge_eq_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:42:40.618822+00:00
-- url     : https://prove2.me/submissions/ea6412cb-4821-4ea4-a71e-a040302fca51

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
theorem _root_.solution (c : G.Coloring (Fin 2)) (e : G.edgeSet) :
    (e : Sym2 V) = s(endA c e, endB c e) :=
  (exists_ends c e).choose_spec.choose_spec.1
end Galvin
