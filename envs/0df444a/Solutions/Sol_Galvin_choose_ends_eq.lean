-- Prove2me | solution 1 for Galvin.choose_ends_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:11:35.102363+00:00
-- url     : https://prove2.me/submissions/782852d8-b4d9-4430-b253-6003bf0533c4

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
public import Definitions.Def_GalvinLib_Orientation
public import Theorems.Thm_Galvin_eq_of_ends

set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace Galvin
theorem _root_.solution (c : G.Coloring (Fin 2)) (e : G.edgeSet)
    (h : ∃ f : G.edgeSet, endA c f = endA c e ∧ endB c f = endB c e) : h.choose = e :=
  eq_of_ends c h.choose_spec.1 h.choose_spec.2
end Galvin
