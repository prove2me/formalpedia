-- Prove2me | solution 1 for Galvin.mem_edge_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:37:55.902134+00:00
-- url     : https://prove2.me/submissions/a59a6120-86ea-407d-a54f-db267505af7a

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
theorem _root_.solution (c : G.Coloring (Fin 2)) (e : G.edgeSet) (v : V) :
    v ∈ (e : Sym2 V) ↔ v = endA c e ∨ v = endB c e := by
  rw [edge_eq_ends c e, Sym2.mem_iff]
end Galvin
