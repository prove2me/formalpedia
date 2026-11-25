-- Prove2me | solution 1 for GalvinMultigraph.degreeB_le_maxDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:51:09.087206+00:00
-- url     : https://prove2.me/submissions/2bee9485-1ab0-4519-8cf5-845d7900e40a

module
public import Definitions.Def_GalvinMultigraph_Gadget
public import Definitions.Def_GalvinLib_Galvin
public import Definitions.Def_GalvinMultigraph_Main
public import Theorems.Thm_LeanPool_Vizing_PEC_Extends_trans


set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph
open Finset
variable {A B E Color : Type*}
namespace GalvinMultigraph
theorem _root_.solution [Fintype A] [Fintype B] (a : E → A) (b : E → B) (y : B) :
    Nat.card {e // b e = y} ≤ maxDegree a b :=
  (Finset.le_sup (f := fun y => Nat.card {e // b e = y}) (mem_univ y)).trans
    (le_max_right _ _)
end GalvinMultigraph
